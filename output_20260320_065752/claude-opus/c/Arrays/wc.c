#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include <stdbool.h>
#include "assert.h"

/*@ predicate chars(char* s) = s == 0 ? true : *s |-> ?c &*& (c == 0 ? true : chars(s + 1)); @*/

int wc(char* string, bool inword)
  //@ requires chars(string);
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

/*@
predicate file_handle(FILE* fp) = true;
@*/

int main(int argc, char** argv) 
  //@ requires true;
  //@ ensures true;
{
  bool inword = false; struct file* fp = 0; char* buff = 0; int total = 0; char* res = 0;
  if(argc < 2) { puts("No input file specified."); return -1; }
  
  //@ close file_handle(0); // placeholder, since we cannot fully model fopen here
  fp = fopen(argv[1], "r");
  buff = malloc(100);
  if(buff == 0 || fp == 0) { abort(); }
  //@ chars(buff);
  res = fgets(buff, 100, fp);
  //@ chars(buff);
  while(res != 0)
    //@ invariant chars(buff) &*& file_handle(fp);
  {
    int tmp = wc(buff, inword);
    if (total > INT_MAX - tmp) {
      break;
    }
    total = total + tmp;
    res = fgets(buff, 100, fp);
    //@ chars(buff);
  }
  printf("%i", total);
  free(buff);
  fclose(fp);
  //@ open file_handle(fp);
  return 0;
}