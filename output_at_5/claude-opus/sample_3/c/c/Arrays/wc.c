#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include <stdbool.h>
#include "assert.h"

/*@
predicate my_string(char* s) = s != 0 &*&
  s[0] |-> ?c &*& (c == 0 ? emp : my_string(s + 1));
@*/

int wc(char* string, bool inword)
  //@ requires my_string(string);
  //@ ensures my_string(string) &*& result >= 0;
{
  char head = * string;
  if(head == 0) {
    return inword ? 1 : 0;
  } else {
    if(head == ' ') {
      int result = wc(string + 1, false);
      return inword ? 1 + result: result;
    } else {
      int result = wc(string + 1, true);
      return result;
    }
  }
}

void test() 
  //@ requires emp;
  //@ ensures emp;
{
  //@ close my_string("This line of text contains 8 words.");
  int nb = wc("This line of text contains 8 words.", false);
  assert(nb == 7);
}

int main(int argc, char** argv) 
  //@ requires true;
  //@ ensures true;
{
  bool inword = false; struct file* fp = 0; char* buff = 0; int total = 0; char* res = 0;
  if(argc < 2) { puts("No input file specified."); return -1; }

  fp = fopen(argv[1], "r");
  buff = malloc(100);
  if(buff == 0 || fp == 0) { abort(); }
  res = fgets(buff, 100, fp);
  while(res != 0)
  //@ invariant total >= 0 &*& buff != 0 &*& my_string(buff);
  {
    int tmp = wc(buff, inword);
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