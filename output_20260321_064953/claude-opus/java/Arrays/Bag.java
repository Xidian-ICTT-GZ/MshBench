class Bag {
  
  int[] a;
  int n;
  
  /*@
  predicate inv() = a != null &*& n >= 0 &*& n <= a.length &*&
                    array_slice(a, 0, n, _);
  @*/
  
  Bag(int[] input)
    //@ requires input != null &*& input.length >= 0;
    //@ ensures inv();
  {
    n = input.length;
    a = new int[n];

    System.arraycopy(input, 0, a, 0, n);
  }
  
  int extractMin()
    //@ requires inv();
    //@ ensures inv();
  {
    //@ open inv();
    int mindex = 0;
    int m = a[mindex];
    for (int i = 1; i < n; i++)
      //@ invariant 1 <= i &*& i <= n &*& inv();
    {
      if (a[i] < m) {
        mindex = i;
        m = a[i];
      }
    }
    n--;
    a[mindex] = a[n];
    //@ close inv();
    return m;
  }
  
}