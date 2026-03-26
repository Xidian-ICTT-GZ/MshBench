import java.util.*;

public class Varargs_desugared
{
  //@ requires l != null && xs != null;
  //@ ensures true;
  public static void addAll(List l,  Object[] xs)
  {
    List temp = Arrays.asList(xs);
    
    l.addAll(temp);
  }

  //@ requires args != null;
  //@ ensures true;
  public static void main(String[] args)
  {
    List l = new ArrayList();
    addAll(l, new Object[]{new Object(), new Object(), new Object()});
  }
}