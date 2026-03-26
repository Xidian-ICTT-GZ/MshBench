#include "stdlib.h"
#include "stdio.h"
#include <stdbool.h>
#include "assert.h"

int main(int argc, char** argv) 
//@ requires argc >= 0 &*& argv != 0 &*& pointers(argv, argc, ?argvs);
//@ ensures true;

{
  struct file* from = 0; struct file* to = 0; char* buffer = 0; int nb_read = 0;
  if(argc < 3) { puts("Not enough parameters."); return -1; }
  
  
  
  //@ open pointers(argv, argc, argvs);
  //@ assert 0 <= 1 &*& 1 < argc;
  //@ assert 0 <= 2 &*& 2 < argc;
  //@ close pointers(argv, argc, argvs);
  from = fopen(argv[1], "r");
  to = fopen(argv[2], "w");
  buffer = malloc(100);
  if(buffer == 0 || from == 0 || to == 0) { abort(); }
  //@ assert buffer != 0;
  //@ assert from != 0;
  //@ assert to != 0;
  //@ assert malloc_block(buffer, 100);
  nb_read = fread(buffer, 1, 100, from);
  while(0 < nb_read)
  //@ invariant buffer != 0 &*& malloc_block(buffer, 100) &*& from != 0 &*& to != 0;
  
  {
    int nb_written = fwrite(buffer, 1, (uintptr_t)nb_read, to);
    
    nb_read = fread(buffer, 1, 100, from);
  }
  fclose(from);
  fclose(to);
  free(buffer);
  return 0;
}