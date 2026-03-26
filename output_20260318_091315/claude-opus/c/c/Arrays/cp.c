#include "stdlib.h"
#include "stdio.h"
#include <stdbool.h>
#include "assert.h"

/*@ 
predicate filep(struct file* f; ) = true;

predicate malloc_block_char(char* p; size_t n) = true;

//@ requires argv != 0 &*& argv[1] != 0 &*& argv[2] != 0;
/*@ 
lemma void fwrite_fread_loop(char* buffer, int nb_read, struct file* from, struct file* to)
  requires malloc_block_char(buffer, 100) &*& filep(from) &*& filep(to) &*& 0 < nb_read &*& nb_read <= 100;
  ensures true;
{
  close_open_file_loop(buffer, nb_read, from, to);
}

lemma void close_open_file_loop(char* buffer, int nb_read, struct file* from, struct file* to)
  requires malloc_block_char(buffer, 100) &*& filep(from) &*& filep(to) &*& nb_read >= 0 &*& nb_read <= 100;
  ensures true;
{
  if(nb_read > 0) {
    // assume fwrite succeeds with nb_read bytes
    close_open_file_loop(buffer, fread(buffer, 1, 100, from), from, to);
  }
}

@*/

int main(int argc, char** argv) 
//@ requires argv != 0 &*& argc >= 0 &*& (forall<int i>; 0 <= i &*& i < argc ==> argv[i] != 0);
//@ ensures true;
{
  struct file* from = 0; struct file* to = 0; char* buffer = 0; int nb_read = 0;
  if(argc < 3) { puts("Not enough parameters."); return -1; }
  
  from = fopen(argv[1], "r");
  to = fopen(argv[2], "w");
  buffer = malloc(100);
  if(buffer == 0 || from == 0 || to == 0) { abort(); }
  nb_read = fread(buffer, 1, 100, from);
  //@ open filep(from);
  while(0 < nb_read)
  //@ invariant malloc_block_char(buffer, 100) &*& filep(from) &*& filep(to) &*& nb_read >= 0 &*& nb_read <= 100;
  {
    int nb_written = fwrite(buffer, 1, (uintptr_t)nb_read, to);
    nb_read = fread(buffer, 1, 100, from);
  }
  fclose(from);
  fclose(to);
  free(buffer);
  return 0;
}