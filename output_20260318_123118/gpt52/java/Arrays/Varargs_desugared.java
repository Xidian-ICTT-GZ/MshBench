import java.util.*;

public class Varargs_desugared
{
  //@ predicate list_pred(List l;) = l != null;
  //@ predicate array_pred(Object[] xs;) = xs != null;

  public static void addAll(List l,  Object[] xs)
  //@ requires list_pred(l) &*& array_pred(xs);
  //@ ensures list_pred(l) &*& array_pred(xs);
  {
    List temp = Arrays.asList(xs);
    l.addAll(temp);
  }

  public static void main(String[] args)
  //@ requires true;
  //@ ensures true;
  {
    List l = new ArrayList();
    addAll(l, new Object[]{new Object(), new Object(), new Object()});
  }
}