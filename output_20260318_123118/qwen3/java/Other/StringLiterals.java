/*@ predicate string_literal(String s;) = true; @*/

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
  
  //@ requires string_literal(s);
  //@ ensures true;
  static public void method(String s)
  {
    
  }
  
  //@ requires string_literal(s);
  //@ ensures true;
  static public void methodFoo(String s)
  {
  }
  
  //@ requires string_literal(s);
  //@ ensures (s == "Bar" ? result == 1 : result == -1);
  //@ ensures (s == "Bar") || (s != "Bar");
  //@ ensures (s == "Bar") ==> (result == 1);
  //@ ensures (s != "Bar") ==> (result == -1);
  static int methodBar(String s)
  {
    if (s.equals("Bar"))
      return 1;
    else
      return -1;
  }
}