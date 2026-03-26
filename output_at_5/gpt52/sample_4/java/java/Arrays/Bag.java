class Bag {
  
  int[] a;
  int n;
  
  /*@
  predicate valid() =
    this.a |-> ?arr &*& this.n |-> ?nn &*& arr != null &*& 0 <= nn &*& nn <= arr.length;
  @*/
  
  Bag(int[] input)
    
    
  //@ requires input != null;
  //@ ensures valid();
  {
    n = input.length;
    a = new int[n];

    
    
    
    
    System.arraycopy(input, 0, a, 0, n);
    
    
    //@ close valid();
  }
  
  int extractMin()
    
    

  //@ requires valid() &*& n > 0;
  //@ ensures valid();
  {
    //@ open valid();
    int mindex = 0;
    
    int m = a[mindex];
    for (int i = 1; i < n; i++)
      
    //@ invariant this.a |-> ?arr &*& this.n |-> ?nn &*& arr != null &*& 0 <= nn &*& nn <= arr.length &*& 1 <= i &*& i <= nn &*& 0 <= mindex &*& mindex < nn;
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