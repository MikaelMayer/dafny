trait Holder<T> {
  var value: T
}

method {:concurrent} Test(holder: Holder<int>)
{
  var x := holder.value + holder.value;
  //x := x + holder.value;
  assert holder.value + holder.value == 2*holder.value;
  assert x == holder.value + holder.value;
}

method {:concurrent} Test2(holder1: Holder<int>, holder2: Holder<int>)
  //modifies holder1, holder2
  requires holder1 != holder2
{
  holder1.value := 2;
  assert holder1.value == 2; // Provable all the time
  holder2.value := 3;
  assert holder1.value == 2; // Not provable in concurrent context
}