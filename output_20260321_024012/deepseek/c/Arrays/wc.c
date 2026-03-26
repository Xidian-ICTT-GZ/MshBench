#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include <stdbool.h>
#include "assert.h"

/*@
predicate chars(char *start, int count) =
    count <= 0 ? true : character(start, _) &*& chars(start + 1, count - 1);
@*/

/*@
fixpoint bool is_space(char c) { return c == ' '; }
fixpoint bool is_zero(char c) { return c == 0; }
@*/

/*@
predicate string(char *s) =
    [?f]chars(s, ?n) &*& n >= 0 &*& character(s + n, 0) &*& [f]chars(s, n);
@*/

int wc(char* string, bool inword)
//@ requires [?f]string(string);
//@ ensures [f]string(string);
{
  
  char head = * string;
  if(head == 0) {
    
    return inword ? 1 : 0;
  } else {
    
    if(head == ' ') {
      //@ open chars(string, ?n);
      //@ assert character(string, head);
      //@ close [f]chars(string, n);
      int result = wc(string + 1, false);
      //@ assert [f]string(string+1);
      //@ close [f]string(string);
      return inword ? 1 + result: result;
    } else {
      //@ open chars(string, ?n);
      //@ assert character(string, head);
      //@ close [f]chars(string, n);
      int result = wc(string + 1, true);
      //@ assert [f]string(string+1);
      //@ close [f]string(string);
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
  //@ chars_split(buff, 99);
  //@ close chars(buff+99, 1);
  //@ close string(buff);
  res = fgets(buff, 100, fp);
  while(res != 0)
  //@ invariant buff |-> ?b &*& [1]string(b) &*& file(fp) &*& res != 0 ? true : true;
  {
    
    
    int tmp = wc(buff, inword);
    
    if (total > INT_MAX - tmp) {
      break;
    }
    total = total + tmp;
    //@ open string(buff);
    //@ chars_join(buff);
    res = fgets(buff, 100, fp);
    //@ if (res != 0) { chars_split(buff, 99); close chars(buff+99, 1); close string(buff); }
  }
  printf("%i", total);
  //@ open string(buff);
  //@ chars_join(buff);
  free(buff);
  fclose(fp);
  return 0;
}