public class StringLiterals
{
  //@ predicate stringLiteral(String s) = true;
  //@ predicate stringLiteralFoo() = true;
  //@ predicate stringLiteralBar() = true;

  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
  {
    String foo = "Foo";
    //@ close stringLiteral(foo);
    //@ close stringLiteralFoo();
    String bar = "Bar";
    //@ close stringLiteral(bar);
    //@ close stringLiteralBar();
    
    method(foo);
    method(bar);
    
    methodFoo(foo);
    int i = 0;
    
    i = methodBar(foo);
    
    i = methodBar(bar);
    
  }
  
  static public void method(String s)
    //@ requires stringLiteral(s);
    //@ ensures stringLiteral(s);
  {
    //@ open stringLiteral(s);
    //@ close stringLiteral(s);
  }
  
  static public void methodFoo(String s)
    //@ requires stringLiteralFoo();
    //@ ensures stringLiteralFoo();
  {
    //@ open stringLiteralFoo();
    //@ close stringLiteralFoo();
  }
  
  static int methodBar(String s)
    //@ requires stringLiteral(s);
    //@ ensures stringLiteral(s) &*& result == 1 || result == -1;
  {
    //@ open stringLiteral(s);
    if (s.equals("Bar"))
      //@ close stringLiteral(s);
      return 1;
    else
      //@ close stringLiteral(s);
      return -1;
  }
}