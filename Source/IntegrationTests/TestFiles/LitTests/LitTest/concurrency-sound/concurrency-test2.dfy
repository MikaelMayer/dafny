trait Role {
  var name: string
  var age: nat
  method RoleSnapshot() returns (name: string, age: nat)
    reads this
    ensures name == this.name && age == this.age
  {
    name := this.name;
    age := this.age;
  }
  method ReplaceWith(name: string, age: nat)
    reads this
    modifies this
    ensures name == this.name && age == this.age
  {
    this.name := name;
    this.age := age;
  }
}

method {:volatile} LogOncall(oncall: Role)
  //reads oncall // TODO: ERror if reads, like "cannot assume oncall is read lock"
{
  var name, age := oncall.name, oncall.age;
  print name, " is currently oncall (", age, " years old)";
  assert name == oncall.name && age == oncall.age;
  name, age := oncall.RoleSnapshot();  // TODO: No modifies and reads check, only compilation
  assert name == oncall.name && age == oncall.age;
}

method {:volatile} ReplaceOncall(oncall: Role, name: string, age: nat)
  //modifies oncall
{
  oncall.name, oncall.age := name, age;
  // oncall.name := 2;
  // oncall.age := 3;
  assert oncall.name == name && oncall.age == age;
  oncall.ReplaceWith(name, age);  // TODO: Emit locks and remove error
  assert oncall.name == name && oncall.age == age;     // Now provable
}

trait Lock {
  ghost function threadsWithLock(): set<nat> reads this
    decreases 0

  predicate Acceptable(threadId: int)
  
  method {:volatile} lock(CURRENT_THREAD_ID: int)
    requires |threadsWithLock()| <= 1
    decreases * // Locally we can't prove something else
    ensures Acceptable(CURRENT_THREAD_ID) ==>
              CURRENT_THREAD_ID in threadsWithLock()
    ensures |threadsWithLock()| <= 1 // Mutual exclusion

  lemma DeadlockFree()

  lemma StarvationFree()
  
  /*method {:volatile} unlock(CURRENT_THREAD_ID: int)
    ensures Acceptable(CURRENT_THREAD_ID) ==>
              CURRENT_THREAD_ID !in threadsWithLock()
    ensures |threadsWithLock| <= old(|threadsWithLock|)
    ensures |threadsWithLock| <= 1 // Mutual exclusivity
    */
}

class LockOne extends Lock {
  var flag1: bool
  var flag2: bool
  var test: bool

  predicate Acceptable(threadId: int) {
    0 <= threadId < 2
  }

  function flagFor(threadId: int): bool reads this
    requires Acceptable(threadId)
  {
    if threadId == 0 then flag1 else flag2
  }


  ghost function threadsWithLock(): set<nat> reads this decreases 0 {
    (if flag1 then {0} else {}) +
    (if flag2 then {1} else {})
  }
  
  method {:volatile} lock(CURRENT_THREAD_ID: int) decreases *
    requires |threadsWithLock()| <= 1
    ensures Acceptable(CURRENT_THREAD_ID) ==>
       CURRENT_THREAD_ID in threadsWithLock()
    ensures |threadsWithLock()| <= 1
  {
    if !Acceptable(CURRENT_THREAD_ID) {
      return;
    }
    if CURRENT_THREAD_ID == 0 {
      this.flag1 := true;
    } else {
      this.flag2 := true;
    }
    assert if CURRENT_THREAD_ID == 0 then flag1 else flag2;
    assert CURRENT_THREAD_ID in threadsWithLock();
    // TODO: control flow should enable to create only one heap.
    var test := flagFor(1-CURRENT_THREAD_ID);
    // Need nonlocal reasoning that can state that
    // CURRENT_THREAD_ID stays in threadsWithLock() 
    while test
      invariant test == flagFor(1-CURRENT_THREAD_ID)
        //if CURRENT_THREAD_ID == 0 then flag2 else flag1
      decreases *
    {
      test := flagFor(1-CURRENT_THREAD_ID);
    } // Autolock for read
    assert |threadsWithLock()| <= 1;
  }
  lemma DeadlockFree()

  lemma StarvationFree()
  /*method {:volatile} unlock(CURRENT_THREAD_ID: int)
    ensures CURRENT_THREAD_ID <= 1 ==>
       CURRENT_THREAD_ID !in threadsWithLock()
    ensures |threadsWithLock| <= 1
  {
    flags[CURRENT_THREAD_ID] := false;
  }*/
}
