class Bag {
  
  int[] a;
  int n;
  
  /*@
  predicate bag() = a |-> ?arr &*& n |-> ?length &*& arr != null &*& length >= 0;
  @*/
  
  Bag(int[] input)
  //@ requires input != null;
  //@ ensures bag();
  {
    n = input.length;
    a = new int[n];
    System.arraycopy(input, 0, a, 0, n);
  }
  
  int extractMin()
  //@ requires bag() &*& n > 0;
  //@ ensures bag() &*& n == old_n - 1;
  {
    int old_n = n;
    int mindex = 0;
    int m = a[mindex];
    for (int i = 1; i < n; i++)
    //@ invariant bag() &*& 1 <= i &*& i <= old_n;
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