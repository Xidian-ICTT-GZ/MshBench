#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include <stdbool.h>
#include "assert.h"

typedef struct file file;
//@ predicate file(FILE *fp;) = true;

int wc(char* string, bool inword)
//@ requires [?f]string(string, ?cs) &*& inword == true || inword == false;
//@ ensures  result >= 0;
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
  //@ close file(fp);
  buff = malloc(100);
  if(buff == 0 || fp == 0) { abort(); }
  res = fgets(buff, 100, fp);
  //@ open file(fp);
  /*@ 
    while(res != 0)
      //@ requires file(fp) &*& malloc_block(buff, 100);
      //@ ensures file(fp) &*& malloc_block(buff, 100);
      //@ invariant file(fp) &*& malloc_block(buff, 100) &*& total >= 0 &*& inword == false;
    {
  @*/
  while(res != 0)
  
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