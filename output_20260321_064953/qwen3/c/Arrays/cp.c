#include "stdlib.h"
#include "stdio.h"
#include <stdbool.h>
#include "assert.h"

/*@
predicate file_handle(FILE* f, bool open) = true;
predicate malloc_block(char* p; int size) = true;
@*/

int main(int argc, char** argv) 
//@ requires true;
//@ ensures true;
{
  struct file* from = 0; struct file* to = 0; char* buffer = 0; int nb_read = 0;
  if(argc < 3) { puts("Not enough parameters."); return -1; }
  
  
  
  from = fopen(argv[1], "r");
  //@ close file_handle(from, true);
  to = fopen(argv[2], "w");
  //@ close file_handle(to, true);
  buffer = malloc(100);
  //@ if (buffer != 0) close malloc_block(buffer, 100);
  if(buffer == 0 || from == 0 || to == 0) { abort(); }
  nb_read = fread(buffer, 1, 100, from);
  while(0 < nb_read)
  //@ invariant file_handle(from, true) &*& file_handle(to, true) &*& malloc_block(buffer, 100);
  {
    int nb_written = fwrite(buffer, 1, (uintptr_t)nb_read, to);
    
    nb_read = fread(buffer, 1, 100, from);
  }
  //@ open file_handle(from, true);
  fclose(from);
  //@ open file_handle(to, true);
  fclose(to);
  //@ open malloc_block(buffer, 100);
  free(buffer);
  return 0;
}