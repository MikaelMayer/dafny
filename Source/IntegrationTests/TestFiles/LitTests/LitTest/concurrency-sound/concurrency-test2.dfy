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