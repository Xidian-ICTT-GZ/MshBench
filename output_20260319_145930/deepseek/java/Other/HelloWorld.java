public class HelloWorld 
{
  //@ predicate HelloWorld() = true;
  
  public HelloWorld()
  //@ requires true;
  //@ ensures HelloWorld();
  {
    //@ close HelloWorld();
  }
  
  public static void main(String[] args) 
  //@ requires true;
  //@ ensures true;
  {
    System.out.println("Hello, World");
  }
}