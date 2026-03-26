/*@ predicate enum_day_valid(enum day d) = d >= 0 &*& d <= 6; @*/

//@ requires true;
//@ ensures enum_day_valid(result);
enum day next_day(enum day d)
{
  return (d + 1) % 7;
}

//@ requires true;
//@ ensures true;
int main() 
{
  enum day d = monday;
  d = 35;
  int x = d;
  assert(large_number == 30000);
  assert(another_large_number == 30001);
  assert(yaln + 1 == -0x7fff);
  return 0;
}