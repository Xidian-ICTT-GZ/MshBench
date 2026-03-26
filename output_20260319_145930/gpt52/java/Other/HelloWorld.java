public class HelloWorld 
{
  //@ requires args == null ? true : args.length >= 0;
  //@ ensures true;
  public static void main(String[] args) 
    
    
  {
    System.out.println("Hello, World");
  }
}