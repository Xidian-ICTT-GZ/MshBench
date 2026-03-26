#include "stdlib.h"
#include "stdio.h"
#include <stdbool.h>
#include "assert.h"

/*@ predicate file_handle(struct file *f; bool is_open) =
      is_open ==> f != 0 &*& valid_file_handle(f);
@*/

/*@ predicate malloc_block(char *p; int n) =
      p != 0 &*& malloc_block(p, n);
@*/

/*@ predicate file_read_buffer(char *buf; int size; int nread) =
      buf != 0 &*& 0 <= nread &*& nread <= size &*&
      malloc_block(buf, size);
@*/

/*@ predicate file_write_buffer(char *buf; int size; int nwritten) =
      buf != 0 &*& 0 <= nwritten &*& nwritten <= size &*&
      malloc_block(buf, size);
@*/

int main(int argc, char **argv)
  //@ requires true;
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

  //@ open true;
  //@ requires true;
  //@ ensures file_handle(from, true) &*& file_handle(to, true);
  from = fopen(argv[1], "r");
  to = fopen(argv[2], "w");

  buffer = malloc(100);
  if (buffer == 0 || from == 0 || to == 0)
  {
    abort();
  }

  //@ open true;
  //@ requires malloc_block(buffer, 100) &*& file_handle(from, true) &*& file_handle(to, true);
  //@ ensures file_read_buffer(buffer, 100, nb_read);
  nb_read = fread(buffer, 1, 100, from);

  while (0 < nb_read)
  //@ invariant file_handle(from, true) &*& file_handle(to, true) &*& malloc_block(buffer, 100) &*&
  //@           file_read_buffer(buffer, 100, nb_read) &*& 0 <= nb_read &*& nb_read <= 100;
  {
    //@ open file_read_buffer(buffer, 100, nb_read);
    //@ requires file_read_buffer(buffer, 100, nb_read) &*& file_handle(to, true);
    //@ ensures file_write_buffer(buffer, 100, nb_written);
    int nb_written = fwrite(buffer, 1, (uintptr_t)nb_read, to);

    //@ open file_write_buffer(buffer, 100, nb_written);
    //@ requires file_handle(from, true) &*& malloc_block(buffer, 100);
    //@ ensures file_read_buffer(buffer, 100, nb_read);
    nb_read = fread(buffer, 1, 100, from);
  }

  //@ requires file_handle(from, true) &*& file_handle(to, true);
  //@ ensures true;
  fclose(from);
  fclose(to);

  //@ requires malloc_block(buffer, 100);
  //@ ensures true;
  free(buffer);
  return 0;
}