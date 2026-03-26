//@ predicate stringLiteral(String s) = true;

public class StringLiterals
{
  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
  {
    String foo = "Foo";
    //@ close stringLiteral(foo);
    String bar = "Bar";
    //@ close stringLiteral(bar);
    
    method(foo);
    method(bar);
    
    methodFoo(foo);
    int i = 0;
    
    i = methodBar(foo);
    
    i = methodBar(bar);
    //@ open stringLiteral(foo);
    //@ open stringLiteral(bar);
  }
  
  static public void method(String s)
    //@ requires stringLiteral(s);
    //@ ensures stringLiteral(s);
  {
    //@ open stringLiteral(s);
    //@ close stringLiteral(s);
  }
  
  static public void methodFoo(String s)
    //@ requires stringLiteral(s);
    //@ ensures stringLiteral(s);
  {
    //@ open stringLiteral(s);
    //@ close stringLiteral(s);
  }
  
  static int methodBar(String s)
    //@ requires stringLiteral(s);
    //@ ensures stringLiteral(s) &*& result == 1 || result == -1;
  {
    //@ open stringLiteral(s);
    if (s.equals("Bar")) {
      //@ close stringLiteral(s);
      return 1;
    } else {
      //@ close stringLiteral(s);
      return -1;
    }
  }
}