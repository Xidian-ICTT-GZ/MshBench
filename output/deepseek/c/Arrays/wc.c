#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include <stdbool.h>
#include "assert.h"

/*@
predicate chars(char *start, int count) =
    count == 0 ?
        true
    :
        character(start, _) &*& chars(start + 1, count - 1);
@*/

/*@
predicate string(char *s) =
    [?f]character(s, ?c) &*& (c == 0 ? true : string(s + 1));
@*/

int wc(char *string, bool inword)
//@ requires string(string);
//@ ensures string(string);
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

/*@
predicate file(struct file *fp) = fp != 0;
@*/

int main(int argc, char **argv)
//@ requires true;
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

  fp = fopen(argv[1], "r");
  //@ close file(fp);
  buff = malloc(100);
  if (buff == 0 || fp == 0)
  {
    abort();
  }
  //@ close chars(buff, 100);
  res = fgets(buff, 100, fp);
  //@ open chars(buff, 100);
  while (res != 0)
  //@ invariant buff != 0 &*& chars(buff, 100) &*& file(fp);
  {
    //@ close string(buff);
    int tmp = wc(buff, inword);
    //@ open string(buff);
    if (total > INT_MAX - tmp)
    {
      break;
    }
    total = total + tmp;
    //@ close chars(buff, 100);
    res = fgets(buff, 100, fp);
    //@ open chars(buff, 100);
  }
  printf("%i", total);
  free(buff);
  //@ open file(fp);
  fclose(fp);
  return 0;
}