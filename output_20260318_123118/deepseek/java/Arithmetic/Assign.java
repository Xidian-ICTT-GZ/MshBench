public class Assign
{
  //@ predicate account(int value) = true;

  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
  {
    int i = 0;
    //@ close account(i);
    
    i = i + 100;
    //@ open account(_);
    //@ close account(i);
    
    i += 100;
    //@ open account(_);
    //@ close account(i);
    
    i -= 1;
    //@ open account(_);
    //@ close account(i);
    
    i %= 99;
    //@ open account(_);
    //@ close account(i);
    //@ open account(_);
  }
}