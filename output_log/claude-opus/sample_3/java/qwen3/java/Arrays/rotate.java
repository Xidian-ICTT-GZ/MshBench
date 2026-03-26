class Program {
  //@ predicate array_range(byte[] xs, int start, int end) =
  //@   0 <= start &*& start <= end &*& end <= xs.length;

  /*@
  predicate rotated_array(byte[] xs, int start, int end) =
    array_range(xs, start, end) &*&
    (end - start)>0 &*&
    exists(int i; 0 <= i &*& i < end - start;
      forall(int j; start <= j &*& j < end;
        xs[j] == xs[(start + ((j - start + i) % (end - start))) % end]
      )
    );
  @*/

  static void rotate(byte[] xs, short start, short end)
    //@ requires array_range(xs, start, end) &*& end - start >= 0;
    //@ ensures array_range(xs, start, end) &*& 
    //@   ((end - start) <= 1 ==> xs == xs) &*& 
    //@   ((end - start) > 1 ==> rotated_array(xs, start, end));
  {
    if (start >= end - 1)
      return;
    byte last = xs[end - 1];

    //@ predicate array_state(byte[] xs_old, byte[] xs_now, int start, int end, int i) = 
    //@   array_range(xs_now, start, end) &*&
    //@   0 <= i &*& i <= end - 1 &*&
    //@   forall(int j; start <= j &*& j < i; xs_now[j + 1] == xs_old[j]) &*&
    //@   forall(int j; i <= j &*& j < end - 1; xs_now[j + 1] == xs_old[j + 1]) &*&
    //@   xs_now[start] == last;

    //@ byte[] xs_old = xs;
    //@ int i = start;
    //@ while (i < end - 1)
      //@ invariant array_state(xs_old, xs, start, end, i);
    {
      xs[i + 1] = xs[i];
      i++;
    }
    xs[start] = last;
  }
}