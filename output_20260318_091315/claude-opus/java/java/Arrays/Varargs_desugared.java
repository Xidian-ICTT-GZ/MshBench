import java.util.*;

public class Varargs_desugared
{
  /*@ predicate list_contents(List l;) = l != null &*& l instanceof ArrayList; @*/

  //@ requires l != null &*& xs != null;
  //@ ensures list_contents(l);
  public static void addAll(List l,  Object[] xs)
  {
    List temp = Arrays.asList(xs);
    //@ close list_contents(temp);
    l.addAll(temp);
    //@ close list_contents(l);
  }

  //@ requires true;
  //@ ensures true;
  public static void main(String[] args)
  {
    List l = new ArrayList();
    //@ close list_contents(l);
    addAll(l, new Object[]{new Object(), new Object(), new Object()});
  }
}