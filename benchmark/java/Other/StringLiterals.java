

public class StringLiterals
{
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
  
  static public void method(String s)
    
    
  {
    
  }
  
  static public void methodFoo(String s)
    
    
  {
  }
  
  static int methodBar(String s)
    
    
  {
    if (s.equals("Bar"))
      return 1;
    else
      return -1;
  }
}
 