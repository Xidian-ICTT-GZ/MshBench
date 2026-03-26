enum day { monday, tuesday, wednesday, thursday, friday, saturday, sunday };

enum large_numbers { large_number = 30000, another_large_number, yaln = -0x7fff - 1 };

/*@ predicate valid_day(enum day d;) = 
      d == monday
  || d == tuesday
  || d == wednesday
  || d == thursday
  || d == friday
  || d == saturday
  || d == sunday;
@*/

enum day next_day(enum day d)
  //@ requires valid_day(d);
  //@ ensures valid_day(result);
{
  return (d + 1) % 7;
}

int main()
  //@ requires true;
  //@ ensures true;
{
  enum day d = monday;

  d = 35;
  int x = d;
  assert(large_number == 30000);
  assert(another_large_number == 30001);
  assert(yaln + 1 == -0x7fff);
  return 0;
}