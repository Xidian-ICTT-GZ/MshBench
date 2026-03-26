public class HelloWorld 
{
  //@ public normal_behavior
  //@ requires true;
  //@ ensures true;
  public static void main(String[] args) 
  {
    System.out.println("Hello, World");
  }
}