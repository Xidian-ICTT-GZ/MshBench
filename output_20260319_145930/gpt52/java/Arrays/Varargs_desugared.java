import java.util.*;

/*@

predicate list_obj(List l) = l != null &*& l.state(?s);

@*/

public class Varargs_desugared
{
  //@ requires list_obj(l) &*& xs != null &*& array_slice(xs, 0, xs.length, ?elems);
  //@ ensures list_obj(l) &*& xs != null &*& array_slice(xs, 0, xs.length, elems);
  public static void addAll(List l,  Object[] xs)
  {
    //@ open list_obj(l);
    List temp = Arrays.asList(xs);
    l.addAll(temp);
    //@ close list_obj(l);
  }

  //@ requires args != null &*& array_slice(args, 0, args.length, ?argElems);
  //@ ensures args != null &*& array_slice(args, 0, args.length, argElems);
  public static void main(String[] args)
  {
    List l = new ArrayList();
    //@ close list_obj(l);
    Object[] arr = new Object[]{new Object(), new Object(), new Object()};
    addAll(l, arr);
    //@ open list_obj(l);
  }
}