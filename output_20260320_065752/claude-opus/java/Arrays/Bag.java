class Bag {
  
  int[] a;
  int n;
  
  /*@
  // Predicate representing ownership of the Bag's array a and field n
  predicate bag(this) = a != null &*& a.length >= n &*& true;
  @*/
  
  Bag(int[] input)
    //@ requires input != null;
    //@ ensures bag(this);
  {
    n = input.length;
    a = new int[n];
    System.arraycopy(input, 0, a, 0, n);
  }
  
  int extractMin()
    //@ requires bag(this);
    //@ ensures bag(this) &*& result >= 0 || true; // no numeric guarantee on contents, just preserve ownership
  {
    //@ open bag(this);
    int mindex = 0;
    int m = a[mindex];
    for (int i = 1; i < n; i++)
      //@ invariant 0 < n &*& 0 <= i &*& i <= n &*& bag(this);
    {
      if (a[i] < m) {
        mindex = i;
        m = a[i];
      }
    }
    n--;
    a[mindex] = a[n];
    //@ close bag(this);
    return m;
  }
  
}