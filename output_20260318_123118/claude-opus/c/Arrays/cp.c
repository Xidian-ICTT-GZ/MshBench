#include "stdlib.h"
#include "stdio.h"
#include <stdbool.h>
#include "assert.h"

/*@ predicate filep(struct file* f) = f != 0; @*/
/*@ predicate bufferp(char* b, size_t n) = b != 0 &*& chars(b, n, _); @*/

int main(int argc, char** argv) 
//@ requires argv != 0 &*& chars((char*)argv, 1, _) &*& true;
//@ ensures  true;
{
  struct file* from = 0; struct file* to = 0; char* buffer = 0; int nb_read = 0;
  if(argc < 3) { puts("Not enough parameters."); return -1; }
  
  from = fopen(argv[1], "r");
  to = fopen(argv[2], "w");
  buffer = malloc(100);
  if(buffer == 0 || from == 0 || to == 0) { abort(); }
  
  //@ open_file(from);
  //@ open_file(to);
  //@ leak filep(from);
  //@ leak filep(to);
  //@ leak bufferp(buffer, 100);
  nb_read = fread(buffer, 1, 100, from);
  /*@ while (0 < nb_read)
      //@ invariant filep(from) &*& filep(to) &*& bufferp(buffer, 100) &*& 0 <= nb_read &*& nb_read <= 100;
    {
      int nb_written = fwrite(buffer, 1, (uintptr_t)nb_read, to);
      
      nb_read = fread(buffer, 1, 100, from);
    }
  @*/
  fclose(from);
  fclose(to);
  free(buffer);
  return 0;
}