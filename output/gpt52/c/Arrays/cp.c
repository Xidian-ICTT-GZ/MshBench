#include "stdlib.h"
#include "stdio.h"
#include <stdbool.h>
#include "assert.h"

/*@

predicate argv_strings(char **argv, int count) =
  count <= 0 ?
    true
  :
    argv[0] |-> ?s &*&
    s != 0 &*&
    chars(s, ?n, ?cs) &*& mem('\0', cs) == true &*&
    argv_strings(argv + 1, count - 1);

@*/

int main(int argc, char **argv)
//@ requires argv != 0 &*& argc >= 0 &*& argv_strings(argv, argc);
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
  nb_read = fread(buffer, 1, 100, from);
  while (0 < nb_read)

  //@ invariant buffer != 0 &*& malloc_block_chars(buffer, 100) &*& 0 <= nb_read;
  {
    int nb_written = fwrite(buffer, 1, (uintptr_t)nb_read, to);

    nb_read = fread(buffer, 1, 100, from);
  }
  fclose(from);
  fclose(to);
  free(buffer);
  return 0;
}