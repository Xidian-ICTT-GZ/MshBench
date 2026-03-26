/*@ predicate main_memory(char c;) = true; @*/

int main()
    //@ requires true;
    //@ ensures true;
{
  char c = 'A';
  return 0;
}