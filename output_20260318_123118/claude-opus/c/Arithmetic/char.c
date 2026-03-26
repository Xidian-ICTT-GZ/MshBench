/*@ 
  predicate main_p() = true;
@*/

int main() 
//@ requires main_p();
//@ ensures main_p();
{
  char c = 'A';
  
  return 0;
}