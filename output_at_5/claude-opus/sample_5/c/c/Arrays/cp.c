#include "stdlib.h"
#include "stdio.h"
#include <stdbool.h>
#include "assert.h"

/*@
predicate filep(struct file* f;) = true;
@*/

int main(int argc, char** argv)
//@ requires argc >= 0 &*& argv != 0;
//@ ensures true;
{
  struct file* from = 0; struct file* to = 0; char* buffer = 0; int nb_read = 0;
  if(argc < 3) { puts("Not enough parameters."); return -1; }

  from = fopen(argv[1], "r");
  to = fopen(argv[2], "w");
  buffer = malloc(100);
  if(buffer == 0 || from == 0 || to == 0) { abort(); }

  nb_read = fread(buffer, 1, 100, from);
  //@ assert 0 <= nb_read &*& nb_read <= 100;
  while(0 < nb_read)
  //@ requires 0 < nb_read &*& nb_read <= 100 &*& buffer != 0 &*& from != 0 &*& to != 0;
  //@ ensures true;
  {
    int nb_written = fwrite(buffer, 1, (uintptr_t)nb_read, to);
    nb_read = fread(buffer, 1, 100, from);
    //@ assert 0 <= nb_read &*& nb_read <= 100;
  }
  fclose(from);
  fclose(to);
  free(buffer);
  return 0;
}