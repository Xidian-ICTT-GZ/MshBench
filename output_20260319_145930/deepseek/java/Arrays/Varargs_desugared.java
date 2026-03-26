import java.util.*;

public class Varargs_desugared
{
  //@ predicate list(List l) = l != null;
  
  public static void addAll(List l,  Object[] xs)
    //@ requires list(l) &*& xs != null;
    //@ ensures list(l);
    
  {
    //@ open list(l);
    List temp = Arrays.asList(xs);
    
    l.addAll(temp);
    //@ close list(l);
  }

  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
    
  {
    List l = new ArrayList();
    //@ close list(l);
    addAll(l, new Object[]{new Object(), new Object(), new Object()});
    //@ open list(l);
  }
}