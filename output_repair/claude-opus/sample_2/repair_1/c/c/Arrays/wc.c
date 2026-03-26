#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include <stdbool.h>
#include "assert.h"

/*@
predicate string(char *s;) =
  character(s, ?c) &*& c == 0 ? true : string(s + 1);
@*/

//@ requires string(string);
//@ ensures string(string);
int wc(char *string, bool inword)
{
  //@ open string(string);
  char head = *string;
  if (head == 0)
  {
    //@ close string(string);
    return inword ? 1 : 0;
  }
  else
  {
    if (head == ' ')
    {
      int result = wc(string + 1, false);
      //@ close string(string);
      return inword ? 1 + result : result;
    }
    else
    {
      int result = wc(string + 1, true);
      //@ close string(string);
      return result;
    }
  }
}

//@ requires true;
//@ ensures true;
void test()
{
  //@ string_literal("This line of text contains 8 words.");
  int nb = wc("This line of text contains 8 words.", false);
  assert(nb == 7);
}

//@ requires 0 <= argc &*& [_]argv(argv, argc, _);
//@ ensures true;
int main(int argc, char **argv) //@ : main
{
  bool inword = false;
  struct file *fp = 0;
  char *buff = 0;
  int total = 0;
  char *res = 0;
  if (argc < 2)
  {
    puts("No input file specified.");
    return -1;
  }

  //@ open [_]argv(argv, argc, _);
  //@ open [_]argv(argv + 1, argc - 1, _);
  fp = fopen(*(argv + 1), "r");
  buff = malloc(100);
  if (buff == 0 || fp == 0)
  {
    abort();
  }
  res = fgets(buff, 100, fp);
  while (res != 0)
    //@ invariant file(fp) &*& chars(buff, 100, _) &*& total >= 0;
  {
    //@ chars_to_string(buff);
    int tmp = wc(buff, inword);
    //@ string_to_chars(buff);
    if (total > INT_MAX - tmp)
    {
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