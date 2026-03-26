/*@ predicate file_handle(void* f); @*/
/*@ predicate allocated(char* p, int n); @*/

//@ requires true;
//@ ensures true;
int main(int argc, char** argv) 
{
  struct file* from = 0; struct file* to = 0; char* buffer = 0; int nb_read = 0;
  if(argc < 3) { puts("Not enough parameters."); return -1; }
  
  from = fopen(argv[1], "r");
  to = fopen(argv[2], "w");
  buffer = malloc(100);
  if(buffer == 0 || from == 0 || to == 0) { abort(); }
  //@ close file_handle(from);
  //@ close file_handle(to);
  //@ close allocated(buffer, 100);
  nb_read = fread(buffer, 1, 100, from);
  while(0 < nb_read)
  //@ invariant file_handle(from) &*& file_handle(to) &*& allocated(buffer, 100) &*& nb_read >= 0;
  {
    int nb_written = fwrite(buffer, 1, (uintptr_t)nb_read, to);
    
    nb_read = fread(buffer, 1, 100, from);
  }
  //@ open file_handle(from);
  //@ open file_handle(to);
  //@ open allocated(buffer, 100);
  fclose(from);
  fclose(to);
  free(buffer);
  return 0;
}