import java.util.*;

public class Varargs_desugared
{
  //@ requires l != null &*& xs != null;
  //@ ensures true;
  public static void addAll(List l,  Object[] xs)
    
    
  {
    //@ close listIsValid(xs, 0);
    List temp = Arrays.asList(xs);
    //@ open listIsValid(xs, 0);
    
    l.addAll(temp);
  }

  //@ requires true;
  //@ ensures true;
  public static void main(String[] args)
    
    
  {
    //@ close listIsValid(new Object[0], 0);
    List l = new ArrayList();
    //@ open listIsValid(new Object[0], 0);
    //@ close listIsValid(new Object[]{new Object(), new Object(), new Object()}, 0);
    addAll(l, new Object[]{new Object(), new Object(), new Object()});
    //@ open listIsValid(new Object[]{new Object(), new Object(), new Object()}, 0);
  }
  
  /*@
  predicate listIsValid(Object[] xs, int i) =
    i <= xs.length &*&
    array_slice(xs, 0, i, _) &*&
    array_slice(xs, i, xs.length - i, unit);
  @*/
}