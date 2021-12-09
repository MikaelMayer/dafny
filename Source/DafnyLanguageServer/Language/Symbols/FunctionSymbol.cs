﻿using System.Collections.Generic;
using System.Linq;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public class FunctionSymbol : MemberSymbol, ILocalizableSymbol {
    public Function Declaration { get; }
    public object Node => Declaration;

    public IList<VariableSymbol> Parameters { get; } = new List<VariableSymbol>();

    /// <summary>
    /// Gets the body of the function
    /// </summary>
    public ScopeSymbol? Body { get; set; }
    public ScopeSymbol? ByMethodBody { get; set; }
    public List<ScopeSymbol> Ens { get; set; } = new();
    public List<ScopeSymbol> Req { get; set; } = new();
    public List<ScopeSymbol> Reads { get; set; } = new();
    public List<ScopeSymbol> Decreases { get; set; } = new();
    public override IEnumerable<ISymbol> Children =>
      Body.AsEnumerable<ISymbol>()
        .Concat(ByMethodBody.AsEnumerable())
        .Concat(Ens)
        .Concat(Req)
        .Concat(Reads)
        .Concat(Decreases)
        .Concat(Parameters);

    public FunctionSymbol(ISymbol? scope, Function function) : base(scope, function) {
      Declaration = function;
    }

    public string GetDetailText(CancellationToken cancellationToken) {
      return $"{Declaration.WhatKind} {TypePrefix}{Declaration.Name}({Declaration.Formals.AsCommaSeperatedText()}): {Declaration.ResultType.AsText()}";
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }
  }
}