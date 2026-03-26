#include "stdio.h"

/*@ predicate argv_block(char **argv, int argc) =
  argc == 0 ?
    emp
  :
    argv[0] |-> ?s &*& s != 0 &*& chars(s, ?cs) &*& argv_block(argv + 1, argc - 1);
*/

/*@ predicate chars(char *s, list<char> cs) =
  s == 0 ?
    cs == nil ? emp : false
  :
    s |-> ?c &*& c != 0 ?
      chars(s + 1, ?cs0) &*& cs == cons(c, cs0)
    :
      cs == nil &*& s |-> 0;
*/

int main(int argc, char **argv) 
//@ requires argc >= 0 &*& argv_block(argv, argc);
//@ ensures true;
{
    for (int i = 0; i < argc; i++)
    //@ invariant 0 <= i &*& i <= argc &*& argv_block(argv, argc);
    {
        puts(*(argv + i));
    }
    return 0;
}