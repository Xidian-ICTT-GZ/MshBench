class Bag {
  
  int[] a;
  int n;
  
  /*@
  predicate this_inv(Bag this) = this.a |-> ?a &*& this.n |-> ?n &*& array(a, int, n, _) &*& a.length >= n;
  @*/
  
  //@ requires input != null &*& input.length >= 0;
  //@ ensures this_inv(this);
  Bag(int[] input)
  //@ open this_inv(this);
  {
    n = input.length;
    a = new int[n];

    System.arraycopy(input, 0, a, 0, n);
  }
  
  //@ requires this_inv(this);
  //@ ensures this_inv(this) &*& result == (?m);
  int extractMin()
  //@ open this_inv(this);
  {
    int mindex = 0;
    int m = a[mindex];
    for (int i = 1; i < n; i++)
    //@ invariant 1 <= i &*& i <= n &*& this_inv(this);
    {
      if (a[i] < m) {
        mindex = i;
        m = a[i];
      }
    }
    n--;
    a[mindex] = a[n];
    //@ close this_inv(this);
    return m;
  }
  
}