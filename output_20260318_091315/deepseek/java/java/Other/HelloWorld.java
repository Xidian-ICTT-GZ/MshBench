public class HelloWorld 
{
  //@ requires true;
  //@ ensures true;
  public static void main(String[] args) 
    
    
  {
    //@ assume args != null;
    System.out.println("Hello, World");
  }
}