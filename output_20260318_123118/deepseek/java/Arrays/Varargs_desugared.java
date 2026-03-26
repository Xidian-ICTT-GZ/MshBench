import java.util.*;

public class Varargs_desugared
{
  //@ predicate list_state(List l, int size) = l != null &*& l.size |-> size;
  //@ predicate array_state(Object[] a, int length) = a != null &*& a.length |-> length &*& array_slice(a, 0, length, _);
  //@ predicate array_slice(Object[] a, int i, int j, list<Object> elems) = i >= 0 &*& i <= j &*& j <= a.length &*& elems == take(j - i, array_to_list(a, i, j)) &*& array_slice_pto(a, i, j, elems);
  //@ predicate array_slice_pto(Object[] a, int i, int j, list<Object> elems) = i == j ? true : a[i] |-> ?v &*& array_slice_pto(a, i + 1, j, tail(elems));
  
  //@ requires list_state(l, ?size_l) &*& array_state(xs, ?len_xs);
  //@ ensures list_state(l, size_l + len_xs);
  public static void addAll(List l,  Object[] xs)
    
    
  {
    List temp = Arrays.asList(xs);
    //@ close list_state(temp, len_xs);
    l.addAll(temp);
    //@ open list_state(temp, len_xs);
  }

  //@ requires true;
  //@ ensures true;
  public static void main(String[] args)
    
    
  {
    List l = new ArrayList();
    //@ close list_state(l, 0);
    //@ close array_state(new Object[]{new Object(), new Object(), new Object()}, 3);
    addAll(l, new Object[]{new Object(), new Object(), new Object()});
    //@ open list_state(l, _);
  }
}