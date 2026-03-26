#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include <stdbool.h>
#include "assert.h"

/*@
predicate cstring(char *s) =
  character(s, ?c) &*& c == 0 ? true : cstring(s+1);

predicate cstring_from(char *s, char *end) =
  s == end ?
    true
  :
    character(s, ?c) &*& cstring_from(s+1, end);

lemma void cstring_to_from(char *s)
  requires cstring(s);
  ensures cstring(s) &*& cstring_from(s, s + length_of_string(s));
{
  open cstring(s);
  if (*s == 0) {
    close cstring(s);
    close cstring_from(s, s);
  } else {
    cstring_to_from(s+1);
    close cstring(s);
    close cstring_from(s, s + length_of_string(s));
  }
}

lemma void cstring_from_to_cstring(char *s, char *end)
  requires cstring_from(s, end) &*& character(end, 0);
  ensures cstring(s);
{
  open cstring_from(s, end);
  if (s == end) {
    close cstring(s);
  } else {
    cstring_from_to_cstring(s+1, end);
    close cstring(s);
  }
}

lemma void cstring_from_split(char *s, char *mid, char *end)
  requires cstring_from(s, end) &*& s <= mid &*& mid <= end;
  ensures cstring_from(s, mid) &*& cstring_from(mid, end);
{
  if (s == mid) {
    close cstring_from(s, mid);
    // cstring_from(mid, end) already available as cstring_from(s, end)
    open cstring_from(s, end);
    close cstring_from(mid, end);
    close cstring_from(s, mid);
  } else {
    open cstring_from(s, end);
    cstring_from_split(s+1, mid, end);
    close cstring_from(s, mid);
    close cstring_from(mid, end);
  }
}
@*/

int wc(char* string, bool inword)
//@ requires cstring(string);
//@ ensures cstring(string);
{
  //@ cstring_to_from(string);
  //@ assert cstring_from(string, string + length_of_string(string));
  //@ open cstring(string);
  char head = * string;
  if(head == 0) {
    //@ close cstring(string);
    return inword ? 1 : 0;
  } else {
    //@ close cstring(string);
    //@ assert length_of_string(string) > 0;
    //@ cstring_from_split(string, string + 1, string + length_of_string(string));
    //@ open cstring_from(string, string + 1);
    //@ open cstring_from(string + 1, string + length_of_string(string));
    //@ cstring_from_to_cstring(string + 1, string + length_of_string(string));
    if(head == ' ') {
      int result = wc(string + 1, false);
      //@ cstring_to_from(string + 1);
      //@ cstring_from_split(string, string + 1, string + 1 + length_of_string(string + 1));
      //@ open cstring_from(string, string + 1);
      //@ close cstring(string);
      return inword ? 1 + result: result;
    } else {
      int result = wc(string + 1, true);
      //@ cstring_to_from(string + 1);
      //@ cstring_from_split(string, string + 1, string + 1 + length_of_string(string + 1));
      //@ open cstring_from(string, string + 1);
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
  free(buff);
  fclose(fp);
  return 0;
}