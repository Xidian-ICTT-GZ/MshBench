import java.util.*;

public class Varargs_desugared
{
  //@ predicate ListState(List l, list<Object> elems) = l != null;
  //@ predicate ArrayListState(ArrayList a, list<Object> elems) = a != null;
  
  public static void addAll(List l,  Object[] xs)
    //@ requires ListState(l, ?elems1) &*& xs != null &*& array_slice(xs, 0, xs.length, ?xsElems);
    //@ ensures ListState(l, ?elems2) &*& elems2 == append(elems1, xsElems) &*& array_slice(xs, 0, xs.length, xsElems);
    
  {
    //@ open ListState(l, elems1);
    //@ close ListState(l, elems1);
    List temp = Arrays.asList(xs);
    //@ close ListState(temp, xsElems);
    l.addAll(temp);
    //@ open ListState(temp, xsElems);
    //@ close ListState(l, append(elems1, xsElems));
  }

  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
    
  {
    List l = new ArrayList();
    //@ close ArrayListState(l, nil);
    //@ close ListState(l, nil);
    addAll(l, new Object[]{new Object(), new Object(), new Object()});
    //@ open ListState(l, _);
    //@ open ArrayListState(l, _);
  }
}