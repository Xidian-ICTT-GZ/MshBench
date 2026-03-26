#include "stdio.h"

/*@ predicate argv_chars(char **argv, int n) =
    n == 0 ? true :
    argv_chars(argv, n-1) &*& *(argv+n-1) != 0;
@*/

int main(int argc, char **argv)
//@ requires argc >= 0 &*& chars_((char *)argv, argc * sizeof(char *), _);
//@ ensures true;
{
  for (int i = 0; i < argc; i++)
  //@ invariant 0 <= i &*& i <= argc &*& chars_((char *)argv, argc * sizeof(char *), _);
  {
    puts(*(argv + i));
  }

  return 0;
}