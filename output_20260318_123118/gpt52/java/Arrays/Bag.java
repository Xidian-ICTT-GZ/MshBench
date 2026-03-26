class Bag {
  
  int[] a;
  int n;
  
  /*@ predicate valid() =
        this.a |-> ?arr &*& this.n |-> ?nn &*& arr != null &*& 0 <= nn &*& nn <= arr.length &*& ints(arr, 0, arr.length, ?vs);
  @*/
  
  Bag(int[] input)
  //@ requires input != null &*& ints(input, 0, input.length, ?vs);
  //@ ensures valid();
  {
    n = input.length;
    a = new int[n];

    System.arraycopy(input, 0, a, 0, n);
  }
  
  int extractMin()
  //@ requires valid() &*& 1 <= n;
  //@ ensures valid();
  {
    int mindex = 0;
    
    int m = a[mindex];
    for (int i = 1; i < n; i++)
    //@ invariant valid() &*& 1 <= n &*& 1 <= i &*& i <= n;
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