#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include <stdbool.h>
#include "assert.h"

/*@
predicate cstring(char *s) =
  character(s, ?c) &*& c == 0 ? true : cstring(s + 1);
@*/

int wc(char* string, bool inword)
//@ requires cstring(string);
//@ ensures cstring(string);
{
  //@ open cstring(string);
  char head = * string;
  if(head == 0) {
    //@ close cstring(string);
    return inword ? 1 : 0;
  } else {
    //@ assert cstring(string + 1);
    if(head == ' ') {
      int result = wc(string + 1, false);
      //@ close cstring(string);
      return inword ? 1 + result: result;
    } else {
      int result = wc(string + 1, true);
      //@ close cstring(string);
      return result;
    }
  }
}

void test() 
//@ requires true;
//@ ensures true;
{
  //@ assume(cstring("This line of text contains 8 words."));
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
  //@ assume(cstring(buff));
  res = fgets(buff, 100, fp);
  //@ assume(res == 0 ? true : cstring(buff));
  while(res != 0)
  //@ invariant buff != 0 &*& cstring(buff);
  {
    
    
    int tmp = wc(buff, inword);
    
    if (total > INT_MAX - tmp) {
      break;
    }
    total = total + tmp;
    res = fgets(buff, 100, fp);
    //@ assume(res == 0 ? true : cstring(buff));
  }
  printf("%i", total);
  //@ open cstring(buff);
  free(buff);
  fclose(fp);
  return 0;
}