public class StringLiterals
{
  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
    
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
  
  static public void method(String s)
    //@ requires true;
    //@ ensures true;
    
  {
    
  }
  
  static public void methodFoo(String s)
    //@ requires true;
    //@ ensures true;
    
  {
  }
  
  static int methodBar(String s)
    //@ requires s != null;
    //@ ensures true;
    
  {
    if (s.equals("Bar"))
      return 1;
    else
      return -1;
  }
}