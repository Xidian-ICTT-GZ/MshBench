import java.util.*;

public class Varargs_desugared
{
  //@ requires l != null &*& xs != null;
  //@ ensures true;
  public static void addAll(List l,  Object[] xs)
    
    
  {
    //@ close listIsAsList(xs);
    List temp = Arrays.asList(xs);
    //@ open listIsAsList(xs);
    
    l.addAll(temp);
  }

  //@ predicate listIsAsList(Object[] xs) = true;
  
  public static void main(String[] args)
    
    
  {
    List l = new ArrayList();
    //@ close listIsAsList(new Object[]{new Object(), new Object(), new Object()});
    addAll(l, new Object[]{new Object(), new Object(), new Object()});
    //@ open listIsAsList(_);
  }
}