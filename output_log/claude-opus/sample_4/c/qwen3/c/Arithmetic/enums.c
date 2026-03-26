enum day { monday, tuesday, wednesday, thursday, friday, saturday, sunday };

enum large_numbers { large_number = 30000, another_large_number = 30001, yaln = -0x7fff - 1 };

/*@ predicate enum_day(enum day d) = 
    d == monday || d == tuesday || d == wednesday || 
    d == thursday || d == friday || d == saturday || d == sunday;
@*/

/*@ predicate enum_large_numbers(enum large_numbers n) = 
    n == large_number || n == another_large_number || n == yaln;
@*/

//@ requires enum_day(d);
//@ ensures result == (d + 1) % 7;
enum day next_day(enum day d)
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
  //@ assert large_number == 30000;
  //@ assert another_large_number == 30001;
  //@ assert yaln + 1 == -0x7fff;
  return 0;
}