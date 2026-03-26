class Bag {
  
  int[] a;
  int n;
  
  /*@
  predicate valid() =
    this.a |-> ?arr &*& this.n |-> ?n0 &*& arr != null &*& 0 <= n0 &*& n0 <= arr.length &*& arr.length |-> _;
  @*/
  
  //@ requires input != null &*& input.length |-> _;
  //@ ensures valid();
  Bag(int[] input)
  {
    n = input.length;
    a = new int[n];
    //@ close valid();
    System.arraycopy(input, 0, a, 0, n);
  }
  
  //@ requires valid() &*& n > 0;
  //@ ensures valid();
  int extractMin()
  {
    //@ open valid();
    int mindex = 0;
    
    int m = a[mindex];
    for (int i = 1; i < n; i++)
    //@ invariant a != null &*& a.length |-> _ &*& 0 <= n &*& n <= a.length &*& 1 <= i &*& i <= n &*& 0 <= mindex &*& mindex < i;
    {
      if (a[i] < m) {
        mindex = i;
        m = a[i];
      }
    }
    n--;
    a[mindex] = a[n];
    //@ close valid();
    return m;
  }
  
}