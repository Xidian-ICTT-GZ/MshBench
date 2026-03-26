#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include <stdbool.h>
#include "assert.h"

/*@ predicate string_chars(char* s; list<char> cs) =
    switch(cs) {
        case nil: return s == 0;
        case cons(c, cs0): return *s == c && string_chars(s + 1, cs0);
    };
@*/

int wc(char* string, bool inword)
//@ requires true;
//@ ensures true;
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
//@ requires true;
//@ ensures true;
{
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
  //@ close chars_(buff, 100, _);
  res = fgets(buff, 100, fp);
  while(res != 0)
  //@ invariant true;
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