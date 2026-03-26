class Bag {
  
  int[] a;
  int n;
  
  /*@
  predicate valid() =
    a != null &*& 0 <= n &*& n <= a.length;
  @*/
  
  //@ requires input != null;
  //@ ensures valid();
  Bag(int[] input)
    
    
  {
    n = input.length;
    a = new int[n];

    
    
    
    
    System.arraycopy(input, 0, a, 0, n);
    
    
  }
  
  //@ requires valid() &*& n > 0;
  //@ ensures valid();
  int extractMin()
    
    

  {
    int mindex = 0;
    
    int m = a[mindex];
    for (int i = 1; i < n; i++)
      
    //@ invariant 1 <= i &*& i <= n &*& 0 <= mindex &*& mindex < n &*& valid();
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