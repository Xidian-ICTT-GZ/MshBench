class Bag {
  
  int[] a;
  int n;
  
  /*@
  predicate this_inv() = a |-> ?arr &*& n |-> ?length;
  @*/
  
  Bag(int[] input)
  //@ requires input != null;
  //@ ensures this_inv();
  {
    n = input.length;
    a = new int[n];
    
    System.arraycopy(input, 0, a, 0, n);
  }
  
  int extractMin()
  //@ requires this_inv() &*& n > 0 &*& a != null;
  //@ ensures this_inv() &*& n == old(n) - 1;
  {
    int mindex = 0;
    int m = a[mindex];
    for (int i = 1; i < n; i++)
    //@ invariant this_inv() &*& 0 <= i &*& i <= n;
    {
      if (a[i] < m) {
        mindex = i;
        m = a[i];
      }
    }
    n--;
    a[mindex] = a[n];
    return m;
  }
}