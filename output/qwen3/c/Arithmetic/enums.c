/*@ predicate enum_day(enum day d) = 
    d == monday || d == tuesday || d == wednesday || 
    d == thursday || d == friday || d == saturday || d == sunday;
@*/

/*@ predicate enum_large_numbers(enum large_numbers n) = 
    n == large_number || n == another_large_number || n == yaln;
@*/

/*@ lemma enum_large_numbers_values()
  requires enum_large_numbers(?n);
  ensures
    (n == large_number ==> large_number == 30000) &
    (n == another_large_number ==> another_large_number == 30001) &
    (n == yaln ==> yaln == -0x7fff - 1);
@*/
//@ proof { }

/*@ requires enum_day(d);
    ensures enum_day(result) &*& result == (d + 1) % 7;
@*/
enum day next_day(enum day d)
{
  return (d + 1) % 7;
}

int main()
{
  enum day d = monday;
  //@ assert enum_day(d);
  d = 35;
  int x = d;
  //@ assert large_number == 30000;
  //@ assert another_large_number == 30001;
  //@ assert yaln + 1 == -0x7fff;
  return 0;
}