import java.util.*;

/*@ predicate list_perm(List l; int size) = true; @*/

public class Varargs_desugared
{
  //@ requires l != null &*& xs != null &*& list_perm(l, _);
  //@ ensures list_perm(l, _);
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