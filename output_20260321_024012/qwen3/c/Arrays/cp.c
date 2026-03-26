//@ #include "stdlib_extra.gh"

#include "stdlib.h"
#include "stdio.h"
#include <stdbool.h>
#include "assert.h"

/*@
predicate file_handle(FILE* f;);
predicate malloc_block(char* p, int size) = chars(p, size, _);
@*/

int main(int argc, char** argv) 
//@ requires true;
//@ ensures true;
{
  struct file* from = 0; struct file* to = 0; char* buffer = 0; int nb_read = 0;
  if(argc < 3) { puts("Not enough parameters."); return -1; }
  
  
  
  from = fopen(argv[1], "r");
  //@ assume(file_handle(from));
  to = fopen(argv[2], "w");
  //@ assume(file_handle(to));
  buffer = malloc(100);
  //@ if (buffer != 0) close malloc_block(buffer, 100);
  if(buffer == 0 || from == 0 || to == 0) { abort(); }
  //@ open malloc_block(buffer, 100);
  nb_read = fread(buffer, 1, 100, from);
  while(0 < nb_read)
  //@ invariant file_handle(from) &*& file_handle(to) &*& chars(buffer, 100, _);
  {
    int nb_written = fwrite(buffer, 1, (uintptr_t)nb_read, to);
    
    nb_read = fread(buffer, 1, 100, from);
  }
  fclose(from);
  fclose(to);
  free(buffer);
  return 0;
}