import java.util.*;

public class Varargs_desugared
{
  //@ requires l != null;
  //@ requires xs != null;
  //@ ensures true;
  public static void addAll(List l,  Object[] xs)
    
    
  {
    //@ open Arrays.asList(xs);
    List temp = Arrays.asList(xs);
    
    l.addAll(temp);
  }

  public static void main(String[] args)
    
    
  {
    List l = new ArrayList();
    //@ close Arrays.asList(new Object[]{new Object(), new Object(), new Object()});
    addAll(l, new Object[]{new Object(), new Object(), new Object()});
  }
}