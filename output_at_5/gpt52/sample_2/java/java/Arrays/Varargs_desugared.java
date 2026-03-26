import java.util.*;

public class Varargs_desugared
{
  public static void addAll(List l,  Object[] xs)
  //@ requires xs != null &*& [_]xs[..] |-> _;
  //@ ensures [_]xs[..] |-> _;
    
    
  {
    //@ array_slice_deep_close(xs, 0, arraylength(xs));
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