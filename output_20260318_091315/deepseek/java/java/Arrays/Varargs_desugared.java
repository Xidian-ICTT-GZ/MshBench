import java.util.*;

public class Varargs_desugared
{
  //@ predicate list(Object l) = true;
  //@ predicate array(Object[] a, int i) = a != null &*& 0 <= i &*& i <= a.length &*& array_slice(a, i, a.length, _);
  
  public static void addAll(List l,  Object[] xs)
    //@ requires list(l) &*& array(xs, 0);
    //@ ensures list(l);
    
  {
    //@ open array(xs, 0);
    List temp = Arrays.asList(xs);
    //@ close list(temp);
    l.addAll(temp);
    //@ open list(temp);
  }

  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
    
  {
    List l = new ArrayList();
    //@ close list(l);
    //@ close array(new Object[]{new Object(), new Object(), new Object()}, 0);
    addAll(l, new Object[]{new Object(), new Object(), new Object()});
    //@ open list(l);
  }
}