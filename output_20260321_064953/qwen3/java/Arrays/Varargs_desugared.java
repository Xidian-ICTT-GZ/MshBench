import java.util.*;

public class Varargs_desugared
{
  /*@
  predicate list(List l;) = true;
  @*/

  public static void addAll(List l,  Object[] xs)
  //@ requires list(l) &*& xs != null;
  //@ ensures list(l);
  {
    List temp = Arrays.asList(xs);
    
    l.addAll(temp);
  }

  public static void main(String[] args)
  //@ requires true;
  //@ ensures true;
  {
    List l = new ArrayList();
    //@ close list(l);
    addAll(l, new Object[]{new Object(), new Object(), new Object()});
  }
}