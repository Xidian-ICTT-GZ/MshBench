#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include <stdbool.h>
#include "assert.h"

int wc(char *string, bool inword)
//@ requires [?f]string(string, ?cs);
//@ ensures [f]string(string, cs);
{
  char head = *string;
  if (head == 0)
  {
    return inword ? 1 : 0;
  }
  else
  {
    if (head == ' ')
    {
      int result = wc(string + 1, false);
      return inword ? 1 + result : result;
    }
    else
    {
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

int main(int argc, char **argv) //@ : main
//@ requires 0 <= argc &*& [_]argv(argv, argc, _);
//@ ensures true;
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
  fp = fopen(argv[1], "r");
  buff = malloc(100);
  if (buff == 0 || fp == 0)
  {
    abort();
  }
  res = fgets(buff, 100, fp);
  while (res != 0)
  //@ invariant chars(buff, 100, _) &*& fp != 0 &*& file(fp) &*& total >= 0;
  {
    //@ chars_to_string(buff);
    int tmp = wc(buff, inword);
    //@ string_to_chars(buff);
    if (total > 2147483647 - tmp)
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