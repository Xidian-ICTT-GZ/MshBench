/*@ predicate main_context() = true; @*/

public class HelloWorld 
{
  //@ requires main_context();
  //@ ensures true;
  public static void main(String[] args) 
  {
    System.out.println("Hello, World");
  }
}