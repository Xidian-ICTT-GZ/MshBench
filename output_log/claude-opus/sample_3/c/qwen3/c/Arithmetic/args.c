#include "stdio.h"

/*@ predicate string_plus(char *s) = 
    s[0] |-> ?c &*& 
    (c == 0 &*& s[1] |-> _ |*& true
    ||   c != 0 &*& string_plus(s + 1));
@*/

/*@ predicate argv_valid(char **argv, int argc) =
    0 <= argc &*&
    malloc_block_char_star(argv, argc * sizeof(char *)) &*&
    (forall int i; 0 <= i && i < argc ==>
        *(argv + i) |-> ?s &*&
        string_plus(s)
    );
@*/

int main(int argc, char **argv)
//@ requires argv_valid(argv, argc);
//@ ensures true;
{
  for (int i = 0; i < argc; i++)
  //@ invariant 0 <= i && i <= argc &*&
  //@           malloc_block_char_star(argv, argc * sizeof(char *)) &*&
  //@           (forall int j; 0 <= j && j < i ==>
  //@               *(argv + j) |-> ?s &*& string_plus(s));
  {
    puts(*(argv + i));
  }

  return 0;
}