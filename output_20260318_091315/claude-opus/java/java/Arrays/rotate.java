class Program {
  /*@ 
   predicate array_slice(byte[] xs, int from, int to; list<byte> elems) = 
     0 <= from &*& from <= to &*& to <= xs.length &*&
     array_slice_impl(xs, from, to, elems);
  
   predicate array_slice_impl(byte[] xs, int i, int to, list<byte> elems) =
     i == to ? elems == nil : 
     xs[i] |-> ?v &*&
     array_slice_impl(xs, i + 1, to, ?rest) &*&
     elems == cons(v, rest);
  @*/

  /*@
    requires 
      xs != null &*& 
      0 <= start &*& start <= end &*& end <= xs.length &*&
      array_slice(xs, 0, xs.length, ?full_elems);
    ensures
      array_slice(xs, 0, xs.length, 
        append(
          take(start, full_elems),
          append(
            cons(nth(full_elems, end - 1), take(end - start - 1, drop(start, full_elems))),
            drop(end, full_elems)
          )
        ));
  @*/
  static void rotate(byte[] xs, short start, short end)
  {
    if (start >= end - 1)
      return;
    byte last = xs[end - 1];
    for (short i = start; i < end - 1; i++)
      //@ invariant start <= i &*& i < end &*& array_slice(xs, 0, xs.length, ?elems);
      {
        xs[i + 1] = xs[i];
      }
    xs[start] = last;
  }
}