#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include <stdbool.h>
#include "assert.h"
#include <limits.h>

/*@
predicate chars(char *start, int count) =
    count <= 0 ? true : character(start, _) &*& chars(start + 1, count - 1);
@*/

//@ predicate file(struct file* fp) = true;

int wc(char* string, bool inword)
//@ requires chars(string, _) &*& string[0] |-> _;
//@ ensures chars(string, _) &*& string[0] |-> _;
{
  char head = * string;
  if(head == 0) {
    //@ close chars(string, 0);
    return inword ? 1 : 0;
  } else {
    if(head == ' ') {
      //@ open chars(string, _);
      int result = wc(string + 1, false);
      //@ close chars(string, _);
      return inword ? 1 + result: result;
    } else {
      //@ open chars(string, _);
      int result = wc(string + 1, true);
      //@ close chars(string, _);
      return result;
    }
  }
}

void test()
//@ requires true;
//@ ensures true;
{
  //@ close chars("This line of text contains 8 words.", 0);
  int nb = wc("This line of text contains 8 words.", false);
  //@ open chars("This line of text contains 8 words.", 0);
  assert(nb == 7);
}

int main(int argc, char** argv)
//@ requires true;
//@ ensures true;
{
  bool inword = false; struct file* fp = 0; char* buff = 0; int total = 0; char* res = 0;
  if(argc < 2) { puts("No input file specified."); return -1; }
  
  fp = fopen(argv[1], "r");
  //@ close file(fp);
  buff = malloc(100);
  if(buff == 0 || fp == 0) { abort(); }
  //@ close chars(buff, 100);
  res = fgets(buff, 100, fp);
  while(res != 0)
  //@ invariant file(fp) &*& chars(buff, 100) &*& 0 <= total;
  {
    //@ open chars(buff, 100);
    int tmp = wc(buff, inword);
    //@ close chars(buff, 100);
    
    if (total > INT_MAX - tmp) {
      break;
    }
    total = total + tmp;
    res = fgets(buff, 100, fp);
  }
  printf("%i", total);
  //@ open chars(buff, 100);
  free(buff);
  //@ open file(fp);
  fclose(fp);
  return 0;
}