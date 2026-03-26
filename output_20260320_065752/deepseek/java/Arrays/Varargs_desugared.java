import java.util.*;

public class Varargs_desugared
{
  //@ requires l != null &*& xs != null;
  //@ ensures true;
  public static void addAll(List l,  Object[] xs)
    
    
  {
    //@ close listIsValid(temp, _);
    List temp = Arrays.asList(xs);
    
    l.addAll(temp);
  }

  //@ requires true;
  //@ ensures true;
  public static void main(String[] args)
    
    
  {
    //@ close listIsValid(l, _);
    List l = new ArrayList();
    addAll(l, new Object[]{new Object(), new Object(), new Object()});
  }
  
  /*@
  predicate listIsValid(List l, int length) = true;
  @*/
}