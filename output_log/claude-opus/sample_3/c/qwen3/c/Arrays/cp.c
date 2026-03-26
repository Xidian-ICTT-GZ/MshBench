#include "stdlib.h"
#include "stdio.h"
#include <stdbool.h>
#include "assert.h"

/*@ predicate file_handle(struct file *f; bool is_open) =
      f != 0 &*& valid_file_handle(f);
@*/

/*@ predicate malloc_block_char(char *p; int n) =
      p != 0 &*& malloc_block(p, n);
@*/

/*@ predicate file_read_buffer(char *buf; int size; int nread) =
      malloc_block_char(buf, size) &*&
      0 <= nread &*& nread <= size;
@*/

/*@ predicate file_write_buffer(char *buf; int size; int nwritten) =
      malloc_block_char(buf, size) &*&
      0 <= nwritten &*& nwritten <= size;
@*/

int main(int argc, char **argv)
  /*@ requires true; @*/
  /*@ ensures true; @*/
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

  /*@ 
    from = fopen(argv[1], "r");
    to = fopen(argv[2], "w");
    //@ open_file_handle(&from);
    //@ open_file_handle(&to);
  @*/
  //@ assert file_handle(from, true) &*& file_handle(to, true);

  buffer = malloc(100);
  if (buffer == 0 || from == 0 || to == 0)
  {
    abort();
  }
  //@ assert malloc_block_char(buffer, 100);

  //@ open file_read_buffer(buffer, 100, 0); // initialize for fread
  nb_read = fread(buffer, 1, 100, from);
  //@ close file_read_buffer(buffer, 100, nb_read);

  while (0 < nb_read)
    //@ invariant file_handle(from, true) &*& file_handle(to, true) &*& malloc_block_char(buffer, 100) &*&
    //@           file_read_buffer(buffer, 100, nb_read) &*& 0 <= nb_read &*& nb_read <= 100;
  {
    //@ open file_read_buffer(buffer, 100, nb_read);
    int nb_written = fwrite(buffer, 1, (uintptr_t)nb_read, to);
    //@ close file_write_buffer(buffer, 100, nb_written);
    // We do not require nwritten == nb_read since fwrite can write fewer bytes.

    //@ open file_write_buffer(buffer, 100, nb_written);
    //@ close file_write_buffer(buffer, 100, 0); // reset write buffer predicate since buffer might change

    //@ close file_handle(from, true);
    //@ close malloc_block_char(buffer, 100);
    nb_read = fread(buffer, 1, 100, from);
    //@ close file_read_buffer(buffer, 100, nb_read);
  }

  //@ open file_handle(from, true);
  //@ open file_handle(to, true);
  fclose(from);
  fclose(to);

  //@ open malloc_block_char(buffer, 100);
  free(buffer);
  return 0;
}