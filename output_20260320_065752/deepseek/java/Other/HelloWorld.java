public class HelloWorld 
{
  //@ requires true;
  //@ ensures true;
  public static void main(String[] args) 
    
    
  {
    //@ close emp();
    System.out.println("Hello, World");
  }
}