public class StringLiterals
{
  //@ predicate StringLiteral(String s) = true;
  
  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
  {
    String foo = "Foo";
    //@ close StringLiteral(foo);
    String bar = "Bar";
    //@ close StringLiteral(bar);
    
    method(foo);
    //@ open StringLiteral(foo);
    method(bar);
    //@ open StringLiteral(bar);
    
    methodFoo(foo);
    //@ open StringLiteral(foo);
    int i = 0;
    
    i = methodBar(foo);
    //@ open StringLiteral(foo);
    
    i = methodBar(bar);
    //@ open StringLiteral(bar);
    
  }
  
  static public void method(String s)
    //@ requires StringLiteral(s);
    //@ ensures StringLiteral(s);
  {
    //@ open StringLiteral(s);
    //@ close StringLiteral(s);
  }
  
  static public void methodFoo(String s)
    //@ requires StringLiteral(s);
    //@ ensures StringLiteral(s);
  {
    //@ open StringLiteral(s);
    //@ close StringLiteral(s);
  }
  
  static int methodBar(String s)
    //@ requires StringLiteral(s);
    //@ ensures StringLiteral(s) &*& result == (s.equals("Bar") ? 1 : -1);
  {
    //@ open StringLiteral(s);
    if (s.equals("Bar"))
      //@ close StringLiteral(s);
      return 1;
    else
      //@ close StringLiteral(s);
      return -1;
  }
}