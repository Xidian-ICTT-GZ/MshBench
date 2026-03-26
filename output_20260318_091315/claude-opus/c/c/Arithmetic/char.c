/*@ 
  predicate main_memory() = true; 
@*/

int main() 
  //@ requires main_memory();
  //@ ensures main_memory();
{
  char c = 'A';
  
  return 0;
}