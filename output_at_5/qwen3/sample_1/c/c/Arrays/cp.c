#include "stdlib.h"
#include "stdio.h"
#include <stdbool.h>
#include "assert.h"

/*@
predicate file_handle(struct file* f) = f != 0;
@*/

//@ requires true;
//@ ensures true;
int main(int argc, char** argv) 
{
  struct file* from = 0; struct file* to = 0; char* buffer = 0; int nb_read = 0;
  if(argc < 3) { puts("Not enough parameters."); return -1; }
  
  //@ requires true;
  //@ ensures true;
  from = fopen(argv[1], "r");
  //@ requires true;
  //@ ensures true;
  to = fopen(argv[2], "w");
  buffer = malloc(100);
  if(buffer == 0 || from == 0 || to == 0) { abort(); }
  
  //@ requires true;
  //@ ensures true;
  nb_read = fread(buffer, 1, 100, from);
  while(0 < nb_read)
  {
    int nb_written = fwrite(buffer, 1, (uintptr_t)nb_read, to);
    
    nb_read = fread(buffer, 1, 100, from);
  }
  
  fclose(from);
  fclose(to);
  free(buffer);
  return 0;
}