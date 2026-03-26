public class Assign
{
  //@ requires true;
  //@ ensures true;
  public static void main(String[] args)
  {
    int i = 0;
    
    //@ assert i == 0;
    i = i + 100;
    //@ assert i == 100;
    
    i += 100;
    //@ assert i == 200;
    
    i -= 1;
    //@ assert i == 199;
    
    //@ assert 99 != 0;
    i %= 99;
    //@ assert i >= 0 &*& i < 99;
  }
}