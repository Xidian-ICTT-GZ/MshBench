//@ predicate string_literal(String s; String value) = true;

public class StringLiterals
{
  //@ requires true;
  //@ ensures true;
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
  //@ ensures true;
  static public void method(String s)
  {
    
  }
  
  //@ requires true;
  //@ ensures true;
  static public void methodFoo(String s)
  {
  }
  
  //@ requires true;
  //@ ensures (s.equals("Bar") &*& result == 1) || (!s.equals("Bar") &*& result == -1);
  static int methodBar(String s)
  {
    if (s.equals("Bar"))
      return 1;
    else
      return -1;
  }
}