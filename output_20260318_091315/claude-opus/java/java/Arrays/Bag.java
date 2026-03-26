class Bag {
  
  int[] a;
  int n;
  
  /*@ predicate bag(int* a, int n, list<int> elems) = 
        0 <= n &*& 
        a |-> ?array &*& array_filled(array, 0, n, ?vals) &*&
        array != null &*&
        array_length(array) >= n &*&
        elems == vals;
  @*/
  
  /*@ 
    requires input != null &*& input.length >= 0 &*& array_filled(input, 0, input.length, ?vals);
    ensures bag(a, n, vals);
  @*/
  Bag(int[] input)
  {
    n = input.length;
    a = new int[n];
    /*@ close bag(a, n, vals); @*/
    
    System.arraycopy(input, 0, a, 0, n);
    //@ open bag(a, n, vals);
    //@ close bag(a, n, vals);
  }
  
  /*@ 
    requires bag(a, n, ?elems) &*& n > 0;
    ensures bag(a, n - 1, ?elems2) &*&
            length(elems) == n &*&
            n - 1 == length(elems2) &*&
            forall<int i; 0 <= i && i < n; true == (index_of(elems, result) == i) &*& result == elems[i]) &*&
            (forall<int x; mem(x, elems2) <==> (mem(x, elems) && x != result));
  @*/
  int extractMin()
  {
    int mindex = 0;
    int m = a[mindex];
    //@ open bag(a, n, ?elems);
    //@ list<int> vals = elems;
    for (int i = 1; i < n; i++)
      /*@ invariant 0 < i &*& i <= n &*& bag(a, n, vals) &*&
                     exists<int min, min_idx; min_idx < i &*& 
                         min == nth(vals, min_idx) &*&
                         forall<int j; 0 <= j && j < i; nth(vals, j) >= min) &*&
                     mindex == min_idx &*& m == min;
      @*/
    {
      if (a[i] < m) {
        mindex = i;
        m = a[i];
      }
    }
    n--;
    a[mindex] = a[n];
    //@ // create elems2 by removing the minimum element at mindex
    //@ list<int> elems2 = remove_at(vals, mindex);
    //@ close bag(a, n, elems2);
    return m;
  }
  
  
  /*@ 
    fixpoint int nth(list<int> l, int i) {
      switch(l) {
        case nil: return 0;
        case cons(h, t): return i == 0 ? h : nth(t, i - 1);
      }
    }
    fixpoint bool mem(int x, list<int> l) {
      switch(l) {
        case nil: return false;
        case cons(h, t): return h == x || mem(x, t);
      }
    }
    fixpoint int index_of(list<int> l, int x) {
      switch(l) {
        case nil: return -1;
        case cons(h, t): return h == x ? 0 : (index_of(t, x) == -1 ? -1 : 1 + index_of(t, x));
      }
    }
    fixpoint list<int> remove_at(list<int> l, int i) {
      switch(l) {
        case nil: return nil;
        case cons(h, t): return i == 0 ? t : cons(h, remove_at(t, i - 1));
      }
    }
  @*/
}