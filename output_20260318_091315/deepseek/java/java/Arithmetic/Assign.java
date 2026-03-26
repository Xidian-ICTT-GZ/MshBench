public class Assign
{
  //@ predicate main_pre() = true;
  //@ predicate main_post() = true;

  public static void main(String[] args)
  //@ requires main_pre();
  //@ ensures main_post();
  {
    int i = 0;
    //@ assert i == 0;
    
    i = i + 100;
    //@ assert i == 100;
    
    i += 100;
    //@ assert i == 200;
    
    i -= 1;
    //@ assert i == 199;
    
    i %= 99;
    //@ assert i == 199 % 99;
    
  }
}