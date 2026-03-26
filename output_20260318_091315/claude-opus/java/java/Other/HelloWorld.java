public class HelloWorld 
{
  public static void main(String[] args) 
  //@ requires args != null &*& args.length >= 0;
  //@ ensures true;
  {
    System.out.println("Hello, World");
  }
}