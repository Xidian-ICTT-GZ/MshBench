public class HelloWorld 
{
  //@ requires true;
  //@ ensures true;
  public static void main(String[] args) 
    
    
  {
    //@ assume(false);
    System.out.println("Hello, World");
  }
}