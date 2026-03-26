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
    
    
  {
    n = input.length;
    a = new int[n];

    
    
    
    
    System.arraycopy(input, 0, a, 0, n);
    
    
  }
  
  //@ requires valid() &*& n > 0;
  //@ ensures valid() &*& result == old(a[?idx]) &*& 0 <= idx &*& idx < old(n);
  int extractMin()
    
    

  {
    //@ open valid();
    int mindex = 0;
    
    int m = a[mindex];
    for (int i = 1; i < n; i++)
      
    //@ invariant a |-> ?arr &*& n |-> ?nn &*& arr != null &*& 0 <= nn &*& nn <= arr.length &*& 1 <= i &*& i <= nn &*& 0 <= mindex &*& mindex < nn;
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