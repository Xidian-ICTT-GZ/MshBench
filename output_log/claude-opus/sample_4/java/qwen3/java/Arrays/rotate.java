class Program {
  //@ predicate array_range(byte[] xs, int start, int end) =
  //@     0 <= start &*& start <= end &*& end <= length(xs);
  //@ predicate rotated_array(byte[] xs, int start, int end) =
  //@     array_range(xs, start, end) &*&
  //@     (end - start > 0) &*&
  //@     (exists(int i; 0 <= i &*& i < end - start;
  //@         (forall(int j; start <= j &*& j < end;
  //@             xs[j] == xs[(start + ((j - start + i) % (end - start))) % end])));
  
  static void rotate(byte[] xs, short start, short end)
    //@ requires array_range(xs, start, end) &*& end - start >= 0;
    //@ ensures array_range(xs, start, end) &*&
    //@         ((end - start <= 1) ==> true) &*&
    //@         ((end - start > 1) ==> rotated_array(xs, start, end));
  {
    if (start >= end - 1)
      return;
    byte last = xs[end - 1];
    //@ int length = end - start;
    //@ byte[] xs_old = xs;
    //@ assert array_range(xs, start, end);
    short i = start;
    //@ // Loop invariant setup:
    //@ // i varies from start up to end - 1
    //@ // For j < i, xs[j + 1] == xs_old[j]
    //@ // For j >= i, xs[j + 1] == xs_old[j + 1]
    //@ // xs[start] == last
    //@ // and array_range(xs, start, end)
    //@ // Also i >= start && i <= end - 1
    //@ 
    //@ // Define the loop invariant:
    //@ (array_range(xs, start, end) &*& 0 <= i &*& i <= end - 1 &*&
    //@  (forall(int j; start <= j &*& j < i;
    //@     xs[j + 1] == xs_old[j])) &*&
    //@  (forall(int j; i <= j &*& j < end - 1;
    //@     xs[j + 1] == xs_old[j + 1])) &*&
    //@  xs[start] == last);
    while(i < end - 1)
      //@ invariant array_range(xs, start, end) &*& 0 <= i &*& i <= end - 1 &*&
      //@           (forall(int j; start <= j &*& j < i;
      //@               xs[j + 1] == xs_old[j])) &*&
      //@           (forall(int j; i <= j &*& j < end - 1;
      //@               xs[j + 1] == xs_old[j + 1])) &*& xs[start] == last;
    {
      xs[i + 1] = xs[i];
      i++;
    }
    xs[start] = last;
  }
}