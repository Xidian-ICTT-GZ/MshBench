class Program {
  //@ predicate array_range(byte[] xs, int start, int end) = 
  //@     0 <= start &*& start <= end &*& end <= length(xs);
  
  //@ predicate rotated_array(byte[] xs, int start, int end) =
  //@     array_range(xs, start, end) &*&
  //@     exists(int i; 0 <= i &*& i < end - start;
  //@         forall(int j; start <= j &*& j < end;
  //@             xs[j] == xs[(start + ((j - start + i) % (end - start))) % end]))
  //@     &*& end - start > 0;

  static void rotate(byte[] xs, short start, short end)
    //@ requires array_range(xs, start, end) &*& end - start >= 0;
    //@ ensures array_range(xs, start, end) &*&
    //@         (end - start <= 1 ==> true) &*&
    //@         (end - start > 1 ==> rotated_array(xs, start, end));
  {
    if (start >= end - 1)
      return;
    byte last = xs[end - 1];
    //@ fixpoint bool array_equal(byte[] a, int a_start, int a_end, byte[] b, int b_start, int b_end) {
    //@   return (a_end - a_start) == (b_end - b_start) &*&
    //@          forall(int k; 0 <= k &*& k < (a_end - a_start); a[a_start + k] == b[b_start + k]);
    //@ }
    //@ fixpoint byte shifted_elem(byte[] a, int start, int end, int i, int j) {
    //@   return a[(start + ((j - start + i) % (end - start))) % end];
    //@ }

    //@ predicate rotated_shifted(byte[] xs, int start, int end, int shift) =
    //@   array_range(xs, start, end) &*& end - start > 1 &*&
    //@   forall(int j; start <= j &*& j < end; xs[j] == xs[(start + ((j - start + shift) % (end - start))) % end]);

    //@ loop_invariant array_range(xs, start, end) &*&
    //@                start <= i &*& i <= end - 1 &*&
    //@                xs[start] == last &*&
    //@                (i == start ==> forall(int j; start <= j &*& j < end - 1;
    //@                                      xs[j + 1] == xs[j])) &*&
    //@                (i > start ==>
    //@                  (forall(int j; start <= j &*& j < i;
    //@                     xs[j + 1] == xs[j]) &*&
    //@                   forall(int j; i <= j &*& j < end - 1;
    //@                     xs[j + 1] == xs[j + 1])));
    for (short i = start; i < end - 1; i++)
    {
      xs[i + 1] = xs[i];
    }
    xs[start] = last;
  }
}