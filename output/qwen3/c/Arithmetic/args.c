#include "stdio.h"

/*@ predicate argv_valid(char **argv, int argc) =
    0 <= argc &*&
    malloc_block_char_star(argv, argc * sizeof(char *)) &*&
    (forall int i; 0 <= i && i < argc ==> 
        *(argv + i) |-> ?s &*&
        malloc_block_char(s, ?n) &*&
        (forall int j; 0 <= j && j < n ==> 
            *(s + j) |-> ?c &*&
            (c == 0 ==> j == n - 1) &*&
            (c != 0 ==> j < n - 1)
        )
    );
@*/

int main(int argc, char **argv)
//@ requires argv_valid(argv, argc);
//@ ensures true;
{
  for (int i = 0; i < argc; i++)
  //@ invariant 0 <= i && i <= argc &*&
  //           malloc_block_char_star(argv, argc * sizeof(char *)) &*&
  //           (forall int j; 0 <= j && j < i ==> 
  //               *(argv + j) |-> ?s &*&
  //               malloc_block_char(s, ?n) &*&
  //               (forall int k; 0 <= k && k < n ==> 
  //                   *(s + k) |-> ?c &*&
  //                   (c == 0 ==> k == n - 1) &*&
  //                   (c != 0 ==> k < n - 1)
  //               )
  //           );
  {
    puts(*(argv + i));
  }

  return 0;
}