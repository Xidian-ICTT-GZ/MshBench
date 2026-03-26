#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include <stdbool.h>
#include "assert.h"

/*@ predicate string(char *s) =
    s != 0 &*& character(s, _) &*& (character(s, 0) || string(s + 1));
@*/

//@ requires string(string);
//@ ensures true;
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
  while (res != 0)
  //@ invariant total >= 0 &*& malloc_block_chars(buff, 100);
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