import java.util.*;

public class Varargs_desugared
{
  /*@
  predicate list(List l) = true;
  @*/

  //@ requires list(l) &*& xs != null;
  //@ ensures list(l);
  public static void addAll(List l,  Object[] xs)
    
    
  {
    //@ open list(l);
    List temp = Arrays.asList(xs);
    
    l.addAll(temp);
    //@ close list(l);
  }

  //@ requires true;
  //@ ensures true;
  public static void main(String[] args)
    
    
  {
    List l = new ArrayList();
    //@ close list(l);
    addAll(l, new Object[]{new Object(), new Object(), new Object()});
  }
}