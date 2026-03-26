#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include <stdbool.h>
#include "assert.h"

/*@
predicate string(char* s;) =
  character(s, ?c) &*& c == 0 ? true : string(s + 1);
@*/

int wc(char* string, bool inword)
//@ requires string(string);
//@ ensures string(string);
{
  //@ open string(string);
  char head = * string;
  if(head == 0) {
    //@ close string(string);
    return inword ? 1 : 0;
  } else {
    
    if(head == ' ') {
      int result = wc(string + 1, false);
      //@ close string(string);
      return inword ? 1 + result: result;
    } else {
      int result = wc(string + 1, true);
      //@ close string(string);
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
  
  
  fp = fopen(*(argv + 1), "r");
  buff = malloc(100);
  if(buff == 0 || fp == 0) { abort(); }
  res = fgets(buff, 100, fp);
  while(res != 0)
  //@ invariant chars(buff, 100, _) &*& file(fp);
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