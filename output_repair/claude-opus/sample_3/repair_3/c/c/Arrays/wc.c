#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include <stdbool.h>
#include "assert.h"

/*@ predicate chars_null_term(char *s) =
    character(s, ?c) &*& (c == 0 || chars_null_term(s + 1));
@*/

//@ requires chars_null_term(string);
//@ ensures chars_null_term(string);
int wc(char *string, bool inword)
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

//@ requires true;
//@ ensures true;
void test()
{
  int nb = wc("This line of text contains 8 words.", false);
  assert(nb == 7);
}

//@ requires true;
//@ ensures true;
int main(int argc, char **argv)
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

  fp = fopen(argv[1], "r");
  buff = malloc(100);
  if (buff == 0 || fp == 0)
  {
    abort();
  }
  res = fgets(buff, 100, fp);
  //@ invariant malloc_block_chars(buff, 100) &*& total >= 0;
  while (res != 0)
  {
    int tmp = wc(buff, inword);
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