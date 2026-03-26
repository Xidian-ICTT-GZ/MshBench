class Bag {
  
  int[] a;
  int n;
  
  /*@ predicate bag(int[] a, int n, list<int> elems) =
        0 <= n &*& n <= a.length &*&
        a |-> ?arr &*& array_segment(arr, 0, n, elems);
  @*/
  
  /*@ predicate array_segment(int[] arr, int start, int end, list<int> elems) =
        start == end ? elems == nil :
        arr |-> ?_ &*& start < end &*&
        acc(arr, start) &*&
        array_segment(arr, start + 1, end, ?tail) &*&
        elems == cons(arr[start], tail);
  @*/
  
  /*@ predicate acc(int[] arr, int i) = true; @*/ 
  
  Bag(int[] input)
    //@ requires input != null &*& input.length >= 0 &*& array_segment(input, 0, input.length, ?elems);
    //@ ensures bag(a, n, elems);
  {
    n = input.length;
    a = new int[n];
    //@ assume bag(a, 0, nil);
    System.arraycopy(input, 0, a, 0, n);
    //@ close array_segment(a, 0, n, elems);
    //@ close bag(a, n, elems);
  }
  
  int extractMin()
    //@ requires bag(a, n, ?elems) &*& n > 0;
    //@ ensures bag(a, n - 1, ?elems0) &*& elems == cons(result, elems0);
  {
    int mindex = 0;
    int m = a[mindex];
    //@ open bag(a, n, elems);
    //@ open array_segment(a, 0, n, elems);
    int i = 1;
    /*@
    invariant 1 <= i &*& i <= n &*&
              bag(a, n, elems) &*&
              length(elems) == n &*&
              m == fold_min(take(i, elems)) &*&
              mindex == index_of_min(take(i, elems));
    @*/
    for (; i < n; i++)
    //@ decreases n - i;
    {
      if (a[i] < m) {
        mindex = i;
        m = a[i];
      }
    }
    n--;
    a[mindex] = a[n];
    //@ close array_segment(a, 0, n, remove_index(elems, mindex));
    //@ close bag(a, n, remove_index(elems, mindex));
    return m;
  }

  /*@ predicate fold_min(list<int> xs, int min) =
        switch(xs) {
          case nil: false;
          case cons(x, nil): min == x;
          case cons(x, xs0): min <= x &*& fold_min(xs0, min);
        };
  @*/
  
  /*@ 
    fixpoint int fold_min(list<int> xs) {
      switch(xs) {
        case nil: return 0; 
        case cons(x, nil): return x;
        case cons(x, xs0):
          int m = fold_min(xs0);
          return m < x ? m : x;
      }
    }
  @*/
  
  /*@ 
    fixpoint list<int> take(int n, list<int> xs) {
      switch(xs) {
        case nil: return nil;
        case cons(x, xs0): return n == 0 ? nil : cons(x, take(n - 1, xs0));
      }
    }
  @*/
  
  /*@ 
    fixpoint int index_of_min_aux(list<int> xs, int idx, int cur_min_idx, int cur_min_val) {
      switch(xs) {
        case nil: return cur_min_idx;
        case cons(x, xs0):
          return (x < cur_min_val) ? index_of_min_aux(xs0, idx + 1, idx, x)
                                 : index_of_min_aux(xs0, idx + 1, cur_min_idx, cur_min_val);
      }
    }
  @*/
  
  /*@ 
    fixpoint int index_of_min(list<int> xs) {
      switch(xs) {
        case nil: return 0; // undefined, won't happen
        case cons(x, xs0): return index_of_min_aux(xs0, 1, 0, x);
      }
    }
  @*/
  
  /*@ 
    fixpoint list<int> remove_index_aux(list<int> xs, int idx, int cur_idx) {
      switch(xs) {
        case nil: return nil;
        case cons(x, xs0): return (idx == cur_idx) ? xs0 : cons(x, remove_index_aux(xs0, idx, cur_idx + 1));
      }
    }
    fixpoint list<int> remove_index(list<int> xs, int idx) {
      return remove_index_aux(xs, idx, 0);
    }
  @*/
}