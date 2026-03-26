import java.util.*;

public class Varargs_desugared
{
  /*@ 
  @*/
  public static void addAll(List l, Object[] xs)
  //@ requires l != null &*& xs != null;
  //@ ensures true;
  {
    List temp = Arrays.asList(xs);
    
    l.addAll(temp);
  }

  /*@ 
  @*/
  public static void main(String[] args)
  //@ requires args != null;
  //@ ensures true;
  {
    List l = new ArrayList();
    addAll(l, new Object[]{new Object(), new Object(), new Object()});
  }
}