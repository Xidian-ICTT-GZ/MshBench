#include "stdlib.h"
#include "stdio.h"
#include <stdbool.h>
#include "assert.h"

/*@

predicate file_handle(struct file *f) = true;

predicate malloc_block_100(char *p) = malloc_block(p, 100);

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
  while(0 < nb_read)
  //@ invariant 0 <= nb_read &*& malloc_block_100(buffer) &*& file_handle(from) &*& file_handle(to);
  {
    int nb_written = fwrite(buffer, 1, (uintptr_t)nb_read, to);
    
    nb_read = fread(buffer, 1, 100, from);
  }
  fclose(from);
  fclose(to);
  free(buffer);
  return 0;
}