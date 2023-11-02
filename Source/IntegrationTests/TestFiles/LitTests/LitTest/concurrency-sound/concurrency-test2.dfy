trait Holder<T> {
  var value: T
}

method {:concurrent} Test(holder: Holder<int>)
{
  var x := holder.value + holder.value;
  assert holder.value + holder.value == 2*holder.value;
  assert x == holder.value + holder.value;
}