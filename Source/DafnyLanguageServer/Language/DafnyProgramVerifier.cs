using Microsoft.Boogie;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;
using System.Diagnostics.CodeAnalysis;
using System.IO;
using System.Text;
using System.Threading;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;
using System;
using System.Text.RegularExpressions;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// dafny-lang based implementation of the program verifier. Since it makes use of static members,
  /// any access is synchronized. Moreover, it ensures that exactly one instance exists over the whole
  /// application lifetime.
  /// </summary>
  /// <remarks>
  /// dafny-lang makes use of static members and assembly loading. Since thread-safety of this is not guaranteed,
  /// this verifier serializes all invocations.
  /// </remarks>
  public class DafnyProgramVerifier : IProgramVerifier {
    private static readonly object InitializationSyncObject = new();
    private static bool initialized;

    private readonly ILogger logger;
    private readonly ILanguageServerFacade languageServer;
    private readonly VerifierOptions options;
    private readonly SemaphoreSlim mutex = new(1);

    private DafnyProgramVerifier(
      ILogger<DafnyProgramVerifier> logger,
      ILanguageServerFacade languageServer,
      VerifierOptions options
      ) {
      this.logger = logger;
      this.languageServer = languageServer;
      this.options = options;
    }

    /// <summary>
    /// Factory method to safely create a new instance of the verifier. It ensures that global/static
    /// settings are set exactly ones.
    /// </summary>
    /// <param name="logger">A logger instance that may be used by this verifier instance.</param>
    /// <param name="languageServer">A instance of the language server</param>
    /// <param name="options">Settings for the verifier.</param>
    /// <returns>A safely created dafny verifier instance.</returns>
    public static DafnyProgramVerifier Create(
      ILogger<DafnyProgramVerifier> logger, ILanguageServerFacade languageServer, IOptions<VerifierOptions> options) {
      lock (InitializationSyncObject) {
        if (!initialized) {
          // TODO This may be subject to change. See Microsoft.Boogie.Counterexample
          //      A dash means write to the textwriter instead of a file.
          // https://github.com/boogie-org/boogie/blob/b03dd2e4d5170757006eef94cbb07739ba50dddb/Source/VCGeneration/Couterexample.cs#L217
          DafnyOptions.O.ModelViewFile = "-";
          DafnyOptions.O.VcsCores = GetConfiguredCoreCount(options.Value);
          initialized = true;
          logger.LogTrace("initialized the boogie verifier...");
        }
        return new DafnyProgramVerifier(logger, languageServer, options.Value);
      }
    }

    private static int GetConfiguredCoreCount(VerifierOptions options) {
      return options.VcsCores == 0
        ? Environment.ProcessorCount / 2
        : Convert.ToInt32(options.VcsCores);
    }

    private static Range? GetMethodRange(string name,
      Dafny.ModuleDefinition module) {
      foreach (var topLevelDecl in module.TopLevelDecls) {
        if (topLevelDecl.FullName == name) {
          return new Range(topLevelDecl.BodyStartTok.line, topLevelDecl.BodyStartTok.col,
               topLevelDecl.BodyEndTok.line, topLevelDecl.BodyEndTok.col);
        }
      }

      return null;
    }


    private static Range? GetMethodRange(string name, Dafny.Program program) {
      foreach (var module in program.Modules()) {
        var range = GetMethodRange(name, module);
        if (range != null) {
          return range;
        }
      }

      return null;
    }

    public VerificationResult Verify(DafnyDocument document, CancellationToken cancellationToken) {
      var program = document.Program;
      mutex.Wait(cancellationToken);
      try {
        // The printer is responsible for two things: It logs boogie errors and captures the counter example model.
        var errorReporter = (DiagnosticErrorReporter)program.reporter;

        string? previouslyVerified = null;
        bool hasErrors = false;
        void VerifyCallback(string s) {
          if (previouslyVerified != null) {
            languageServer.TextDocument.SendNotification(new VerificationIntermediateParams {
              Uri = document.Uri,
              Version = document.Version,
              MethodName = previouslyVerified,
              Verified = !hasErrors,
              Range = GetMethodRange(previouslyVerified, document.Program)
            });
          }
          previouslyVerified = s;
          hasErrors = false;
        }
        void VerifyStatusCallback(string s) {
          if (s == "error" || s == "errors") {
            hasErrors = true;
          }
        }

        var printer = new ModelCapturingOutputPrinter(logger, errorReporter, VerifyCallback, VerifyStatusCallback);
        ExecutionEngine.printer = printer;
        // Do not set the time limit within the construction/statically. It will break some VerificationNotificationTest unit tests
        // since we change the configured time limit depending on the test.
        DafnyOptions.O.TimeLimit = options.TimeLimit;
        var translated = Translator.Translate(program, errorReporter, new Translator.TranslatorFlags { InsertChecksums = true });
        bool verified = true;
        foreach (var (_, boogieProgram) in translated) {
          cancellationToken.ThrowIfCancellationRequested();
          var verificationResult = VerifyWithBoogie(boogieProgram, cancellationToken);
          verified = verified && verificationResult;
        }
        return new VerificationResult(verified, printer.SerializedCounterExamples);
      }
      finally {
        mutex.Release();
      }
    }

    private bool VerifyWithBoogie(Boogie.Program program, CancellationToken cancellationToken) {
      program.Resolve();
      program.Typecheck();

      ExecutionEngine.EliminateDeadVariables(program);
      ExecutionEngine.CollectModSets(program);
      ExecutionEngine.CoalesceBlocks(program);
      ExecutionEngine.Inline(program);
      // TODO Is the programId of any relevance? The requestId is used to cancel a verification.
      //      However, the cancelling a verification is currently not possible since it blocks a text document
      //      synchronization event which are serialized. Thus, no event is processed until the pending
      //      synchronization is completed.
      var uniqueId = Guid.NewGuid().ToString();
      using (cancellationToken.Register(() => CancelVerification(uniqueId))) {
        try {
          var statistics = new PipelineStatistics();
          var outcome = ExecutionEngine.InferAndVerify(program, statistics, uniqueId, error => { }, uniqueId);
          return Main.IsBoogieVerified(outcome, statistics);
        } catch (Exception e) when (e is not OperationCanceledException) {
          if (!cancellationToken.IsCancellationRequested) {
            throw;
          }
          // It appears that Boogie disposes resources that are still in use upon cancellation.
          // Therefore, we log this error and proceed with the cancellation.
          logger.LogDebug(e, "boogie error occured when cancelling the verification");
          throw new OperationCanceledException(cancellationToken);
        }
      }
    }

    private void CancelVerification(string requestId) {
      logger.LogDebug("requesting verification cancellation of {RequestId}", requestId);
      ExecutionEngine.CancelRequest(requestId);
    }

    private class ModelCapturingOutputPrinter : OutputPrinter {
      private readonly ILogger logger;
      private readonly DiagnosticErrorReporter errorReporter;
      private readonly Action<string> onVerify;
      private readonly Action<string> onVerifyStatus;
      private StringBuilder? serializedCounterExamples;

      public string? SerializedCounterExamples => serializedCounterExamples?.ToString();


      private const string VerifyRegexStr = @"Verifying CheckWellformed\$\$_module\.(?:__default\.)?(\S*)";
      private const string VerifyStatusRegexStr = @"^\s*(verified|error|errors)$";
      private Regex verifyRegex;
      private Regex verifyStatusRegex;
      public ModelCapturingOutputPrinter(
          ILogger logger, DiagnosticErrorReporter errorReporter,
          Action<String> onVerify,
          Action<String> onVerifyStatus) {
        this.logger = logger;
        this.errorReporter = errorReporter;
        this.onVerify = onVerify;
        this.onVerifyStatus = onVerifyStatus;
        verifyRegex = new Regex(VerifyRegexStr);
        verifyStatusRegex = new Regex(VerifyStatusRegexStr);
      }

      public void AdvisoryWriteLine(string format, params object[] args) {
      }

      public void ErrorWriteLine(TextWriter tw, string s) {
        Match match = verifyRegex.Match(s);
        if (match.Success) {
          onVerify("" + match.Groups[0]);
        }

        match = verifyStatusRegex.Match(s);
        if (match.Success) {
          onVerifyStatus("" + match.Groups[0]);
        }
        logger.LogError(s);
      }

      public void ErrorWriteLine(TextWriter tw, string format, params object[] args) {
        logger.LogError(format, args);
      }

      public void Inform(string s, TextWriter tw) {
        logger.LogInformation(s);
      }

      public void ReportBplError(IToken tok, string message, bool error, TextWriter tw, [AllowNull] string category) {
        logger.LogError(message);
      }

      public void WriteErrorInformation(ErrorInformation errorInfo, TextWriter tw, bool skipExecutionTrace) {
        CaptureCounterExamples(errorInfo);
        errorReporter.ReportBoogieError(errorInfo);
      }

      private void CaptureCounterExamples(ErrorInformation errorInfo) {
        if (errorInfo.Model is StringWriter modelString) {
          // We do not know a-priori how many errors we'll receive. Therefore we capture all models
          // in a custom stringbuilder and reset the original one to not duplicate the outputs.
          serializedCounterExamples ??= new StringBuilder();
          serializedCounterExamples.Append(modelString.ToString());
          modelString.GetStringBuilder().Clear();
        }
      }

      public void WriteTrailer(PipelineStatistics stats) {
      }
    }
  }
}
