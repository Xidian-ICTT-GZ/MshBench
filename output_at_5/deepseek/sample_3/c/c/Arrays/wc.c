#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include <stdbool.h>
#include "assert.h"

/*@
predicate chars(char *start, int count) =
    count <= 0 ? true : character(start, _) &*& chars(start + 1, count - 1);
@*/

int wc(char* string, bool inword)
//@ requires [?f]chars(string, ?n) &*& mem('\0', string, n) == true;
//@ ensures [f]chars(string, n);
{
  
  char head = * string;
  if(head == 0) {
    
    return inword ? 1 : 0;
  } else {
    
    if(head == ' ') {
      //@ open chars(string, n);
      //@ assert character(string, head);
      int result = wc(string + 1, false);
      //@ close [f]chars(string, n);
      return inword ? 1 + result: result;
    } else {
      //@ open chars(string, n);
      //@ assert character(string, head);
      int result = wc(string + 1, true);
      //@ close [f]chars(string, n);
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
  //@ chars__split(buff, 100);
  res = fgets(buff, 100, fp);
  while(res != 0)
  //@ invariant buff |-> ?b &*& [1/2]chars(b, 100) &*& file(fp) &*& res != 0 ? [1/2]chars(b, 100) : true;
  {
    
    //@ open [1/2]chars(b, 100);
    int tmp = wc(buff, inword);
    //@ close [1/2]chars(b, 100);
    
    if (total > INT_MAX - tmp) {
      break;
    }
    total = total + tmp;
    res = fgets(buff, 100, fp);
  }
  printf("%i", total);
  //@ chars__join(buff);
  free(buff);
  fclose(fp);
  return 0;
}