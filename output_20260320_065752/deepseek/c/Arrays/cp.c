#include "stdlib.h"
#include "stdio.h"
#include <stdbool.h>
#include "assert.h"

//@ predicate file(struct file* f;);

int main(int argc, char** argv) 
//@ requires true;
//@ ensures true;
{
  struct file* from = 0; struct file* to = 0; char* buffer = 0; int nb_read = 0;
  if(argc < 3) { puts("Not enough parameters."); return -1; }
  
  //@ assume(argv[1] != 0);
  //@ assume(argv[2] != 0);
  from = fopen(argv[1], "r");
  to = fopen(argv[2], "w");
  buffer = malloc(100);
  if(buffer == 0 || from == 0 || to == 0) { abort(); }
  //@ close file(from);
  //@ close file(to);
  //@ chars(buffer, 100, _);
  nb_read = fread(buffer, 1, 100, from);
  while(0 < nb_read)
  //@ invariant file(from) &*& file(to) &*& chars(buffer, 100, _);
  {
    int nb_written = fwrite(buffer, 1, (uintptr_t)nb_read, to);
    //@ open file(to);
    //@ close file(to);
    nb_read = fread(buffer, 1, 100, from);
    //@ open file(from);
    //@ close file(from);
  }
  //@ open file(from);
  fclose(from);
  //@ open file(to);
  fclose(to);
  //@ open chars(buffer, 100, _);
  free(buffer);
  return 0;
}