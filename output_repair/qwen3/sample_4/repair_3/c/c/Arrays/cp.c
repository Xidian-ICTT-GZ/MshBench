#include "stdlib.h"
#include "stdio.h"
#include <stdbool.h>
#include "assert.h"

int main(int argc, char **argv)
//@ requires 3 <= argc &*& [_]argv(argv, argc, ?vs) &*& vs != 0 &*& pointer(vs + 1) &*& *(vs + 1) != 0 &*& pointer(vs + 2) &*& *(vs + 2) != 0;
//@ ensures true;
{
  struct file *from = 0;
  struct file *to = 0;
  char *buffer = 0;
  int nb_read = 0;
  if (argc < 3)
  {
    puts("Not enough parameters.");
    return -1;
  }

  from = fopen(argv[1], "r");
  to = fopen(argv[2], "w");
  buffer = malloc(100);
  if (buffer == 0 || from == 0 || to == 0)
  {
    abort();
  }
  //@ open malloc_block(buffer, 100);
  nb_read = fread(buffer, 1, 100, from);
  while (0 < nb_read)
  //@ invariant file(from) &*& file(to) &*& chars(buffer, 100, _) &*& malloc_block(buffer, 100);
  {
    int nb_written = fwrite(buffer, 1, (uintptr_t)nb_read, to);

    nb_read = fread(buffer, 1, 100, from);
  }
  fclose(from);
  fclose(to);
  free(buffer);
  return 0;
}