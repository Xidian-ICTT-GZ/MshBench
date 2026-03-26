class Bag {
  
  int[] a;
  int n;
  
  /*@
  predicate inv() =
    this.a |-> ?arr &*& this.n |-> ?nn &*& arr != null &*& 0 <= nn &*& nn <= arr.length &*& ints(arr, 0, arr.length, ?vs);
  @*/
  
  Bag(int[] input)
  //@ requires input != null &*& ints(input, 0, input.length, ?vs);
  //@ ensures ints(input, 0, input.length, vs) &*& inv();
  {
    //@ close inv();
    //@ open inv();
    n = input.length;
    a = new int[n];

    
    
    
    
    System.arraycopy(input, 0, a, 0, n);
    //@ close inv();
    
    
  }
  
  int extractMin()
  //@ requires inv() &*& 1 <= n;
  //@ ensures inv();
  {
    //@ open inv();
    int mindex = 0;
    
    int m = a[mindex];
    for (int i = 1; i < n; i++)
      //@ invariant this.a |-> ?arr &*& this.n |-> ?nn &*& arr != null &*& 1 <= nn &*& nn <= arr.length &*& ints(arr, 0, arr.length, ?vs) &*& 1 <= i &*& i <= nn &*& 0 <= mindex &*& mindex < nn;
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