/*@ predicate list(List l; int size) = true; @*/

import java.util.*;

public class Varargs_desugared
{
  //@ requires list(l, _) &*& xs != null &*& array_slice(xs, 0, xs.length, _);
  //@ ensures list(l, _) &*& array_slice(xs, 0, xs.length, _);
  public static void addAll(List l,  Object[] xs)
  {
    List temp = Arrays.asList(xs);
    
    l.addAll(temp);
  }

  public static void main(String[] args)
  {
    List l = new ArrayList();
    addAll(l, new Object[]{new Object(), new Object(), new Object()});
  }
}