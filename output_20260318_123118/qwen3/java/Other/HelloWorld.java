/*@ predicate main_pre() = true; @*/

public class HelloWorld 
{
  //@ requires main_pre();
  //@ ensures true;
  public static void main(String[] args) 
  {
    System.out.println("Hello, World");
  }
}