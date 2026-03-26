import java.util.*;

public class Varargs_desugared
{
  /*@ 
  predicate list_elements(List l; int n) =
    l instanceof java.util.ArrayList &*& l.size() == n &*& true;
  @*/

  //@ requires l != null &*& xs != null;
  //@ requires list_elements(l; ?n);
  //@ ensures list_elements(l; n + xs.length);
  public static void addAll(List l,  Object[] xs)
  {
    List temp = Arrays.asList(xs);
    //@ // temp is a fixed-size list backed by xs array, so owns xs.length elements
    //@ leak list_elements(temp; xs.length);
    l.addAll(temp);
  }

  //@ requires true;
  //@ ensures true;
  public static void main(String[] args)
  {
    List l = new ArrayList();
    //@ close list_elements(l; 0);
    addAll(l, new Object[]{new Object(), new Object(), new Object()});
  }
}