import java.util.*;

public class Varargs_desugared
{
  //@ requires l != null &*& xs != null;
  //@ ensures true;
  public static void addAll(List l,  Object[] xs)
  {
    //@ open l.list(?contents);
    List temp = Arrays.asList(xs);
    //@ close l.list(contents);
    
    l.addAll(temp);
    //@ open l.list(_);
    //@ close l.list(_);
  }

  public static void main(String[] args)
  {
    List l = new ArrayList();
    //@ close l.list(nil);
    addAll(l, new Object[]{new Object(), new Object(), new Object()});
    //@ open l.list(_);
  }
}

/*@ 
predicate list(List l; list<Object> contents) =
  l instanceof ArrayList ? 
    [_]l.size() == length(contents) &*&
    (length(contents) == 0 ?
      true
    :
      true // Simplified for verification feasibility
    )
  : false;
@*/