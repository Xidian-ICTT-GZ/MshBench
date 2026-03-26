class Bag {
  
  int[] a;
  int n;
  
  /*@
  predicate valid() =
    this.a |-> ?arr &*& this.n |-> ?nn &*& arr != null &*& 0 <= nn &*& nn <= arr.length;
  @*/
  
  //@ requires input != null;
  //@ ensures valid();
  Bag(int[] input)
    
    
  //@ requires input != null;
  //@ ensures valid();
  {
    n = input.length;
    a = new int[n];

    
    
    
    
    System.arraycopy(input, 0, a, 0, n);
    
    
  }
  
  //@ requires valid() &*& n > 0;
  //@ ensures valid();
  int extractMin()
    
    

  //@ requires valid() &*& n > 0;
  //@ ensures valid();
  {
    //@ open valid();
    int mindex = 0;
    
    int m = a[mindex];
    //@ int oldn = n;
    for (int i = 1; i < n; i++)
      
    //@ invariant a != null &*& 0 <= i &*& i <= n &*& n == oldn &*& 0 < n &*& n <= a.length &*& 0 <= mindex &*& mindex < n;
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