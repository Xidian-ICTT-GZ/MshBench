public class StringLiterals
{
  //@ requires true;
  public static void main(String[] args)
  {
    String foo = "Foo";
    String bar = "Bar";
    
    method(foo);
    method(bar);
    
    methodFoo(foo);
    int i = 0;
    
    i = methodBar(foo);
    
    i = methodBar(bar);
    
  }
  
  //@ requires true;
  static public void method(String s)
  {
    
  }
  
  //@ requires true;
  static public void methodFoo(String s)
  {
  }
  
  //@ requires true;
  //@ ensures result == 1 || result == -1;
  static int methodBar(String s)
  {
    if (s.equals("Bar"))
      return 1;
    else
      return -1;
  }
}