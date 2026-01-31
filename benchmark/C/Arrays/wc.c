#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include <stdbool.h>
#include "assert.h"

/*@
fixpoint int wcount(list<char> cs, bool inword) {
  switch(cs) {
    case nil: return inword ? 1 : 0;
    case cons(h, t): return 0 == h ? (inword ? 1 : 0) : (' ' == h ? ((inword ? 1 : 0) + wcount(t, false)) : wcount(t, true));
  }
}

lemma void wcount_in_range(list<char> cs, bool inword)
  requires true;
  ensures wcount(cs, inword) >= 0 &*& wcount(cs, inword) <= length(cs) + 1;
{
  switch(cs) {
    case nil:
      // Base case: if the list is empty, wcount(cs, inword) is either 0 or 1,
      // and length(cs) is 0, so the result is valid.
      if (inword) {
        assert wcount(cs, inword) == 1;
      } else {
        assert wcount(cs, inword) == 0;
      }
      assert wcount(cs, inword) <= length(cs) + 1;
      break;
    case cons(h, t):
      // Recursive case: process the head and the tail of the list.
      wcount_in_range(t, false); // Call lemma for tail with false
      wcount_in_range(t, true);  // Call lemma for tail with true
      if (h == 0) {
        // If head is the null character, wcount(cs, inword) is either 0 or 1,
        // which is still less than or equal to length(cs).
        assert wcount(cs, inword) == (inword ? 1 : 0);
      } else if (h == ' ') {
        // If the head is a space, the wcount either increments or remains the same.
        // The word count is still less than or equal to the total length.
        assert wcount(cs, inword) == (inword ? 1 + wcount(t, false) : wcount(t, false));
      } else {
        // If the head is a non-space character, we proceed with the count from the tail.
        assert wcount(cs, inword) == wcount(t, true);
      }
      // Finally, assert that wcount(cs, inword) is less than or equal to length(cs).
      assert wcount(cs, inword) <= length(cs) + 1;
      break;
  }
}
@*/

int wc(char* string, bool inword)
//@ requires [?f]string(string, ?cs) &*& wcount(cs, inword) < INT_MAX;
//@ ensures [f]string(string, cs) &*& result == wcount(cs, inword);
{
  //@ open [f]string(string, cs);
  char head = * string;
  if(head == 0) {
    //@ close [f]string(string, cs);
    return inword ? 1 : 0;
  } else {
    //@ string_limits(string);
    if(head == ' ') {
      int result = wc(string + 1, false);
      //@ close [f]string(string, cs);
      return inword ? 1 + result: result;
    } else {
      int result = wc(string + 1, true);
      //@ close [f]string(string, cs);
      return result;
    }
  }
}

void test() 
//@ requires true;
//@ ensures true;
{
  int nb = wc("This line of text contains 8 words.", false);
  assert(nb == 7);
}

int main(int argc, char** argv) //@ : main
//@ requires 0 <= argc &*& [_]argv(argv, argc, _);
//@ ensures true;
{
  bool inword = false; struct file* fp = 0; char* buff = 0; int total = 0; char* res = 0;
  if(argc < 2) { puts("No input file specified."); return -1; }
  //@ open [_]argv(argv, argc, _);
  //@ open [_]argv(argv + 1, argc - 1, _);
  fp = fopen(argv[1], "r");
  buff = malloc(100);
  if(buff == 0 || fp == 0) { abort(); }
  res = fgets(buff, 100, fp);
  while(res != 0)
  //@ invariant file(fp) &*& res != 0 ? string(buff, ?scs) &*& buff[length(scs) + 1..100] |-> _ : buff[..100] |-> _;
  {
    //@ assert string(buff, ?scs);
    //@ wcount_in_range(scs, inword);
    int tmp = wc(buff, inword);
    //@ string_to_chars(buff);
    if (total > INT_MAX - tmp) {
      break;
    }
    total = total + tmp;
    res = fgets(buff, 100, fp);
  }
  printf("%i", total);
  free(buff);
  fclose(fp);
  return 0;
}