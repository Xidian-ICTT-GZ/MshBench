#include "stdlib.h"
#include "stdio.h"
#include <stdbool.h>
#include "assert.h"

/*@ predicate file_handle(FILE* f); @*/

int main(int argc, char** argv) 
//@ requires true;
//@ ensures true;
{
  struct file* from = 0; struct file* to = 0; char* buffer = 0; int nb_read = 0;
  if(argc < 3) { puts("Not enough parameters."); return -1; }
  
  
  
  from = fopen(argv[1], "r");
  //@ close file_handle(from);
  to = fopen(argv[2], "w");
  //@ close file_handle(to);
  buffer = malloc(100);
  //@ close chars(buffer, 100, _);
  if(buffer == 0 || from == 0 || to == 0) { abort(); }
  nb_read = fread(buffer, 1, 100, from);
  while(0 < nb_read)
  //@ invariant file_handle(from) &*& file_handle(to) &*& chars(buffer, 100, _);
  {
    int nb_written = fwrite(buffer, 1, (uintptr_t)nb_read, to);
    
    nb_read = fread(buffer, 1, 100, from);
  }
  //@ open file_handle(from);
  fclose(from);
  //@ open file_handle(to);
  fclose(to);
  //@ open chars(buffer, 100, _);
  free(buffer);
  return 0;
}