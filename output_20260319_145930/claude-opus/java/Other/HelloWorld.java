public class HelloWorld 
{
  public static void main(String[] args) 
    //@ requires true;
    //@ ensures true;
  {
    System.out.println("Hello, World");
  }
}