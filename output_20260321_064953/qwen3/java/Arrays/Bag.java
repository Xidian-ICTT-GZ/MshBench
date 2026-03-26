class Bag {
  
  /*@
  predicate bag_pred() = a |-> ?arr &*& n |-> ?len &*& array_slice(arr, 0, len, _);
  @*/
  
  int[] a;
  int n;
  
  
  
  //@ requires input != null &*& array_slice(input, 0, input.length, _);
  //@ ensures bag_pred();
  Bag(int[] input)
    
    
  {
    n = input.length;
    a = new int[n];

    
    
    
    
    System.arraycopy(input, 0, a, 0, n);
    
    
  }
  
  //@ requires bag_pred() &*& n > 0;
  //@ ensures bag_pred() &*& result == old_val(a[?i]) &*& 0 <= i &*& i < old_val(n);
  int extractMin()
    
    

  {
    //@ open bag_pred();
    int mindex = 0;
    
    int m = a[mindex];
    for (int i = 1; i < n; i++)
      

    {
      //@ invariant 1 <= i &*& i <= n &*& mindex >= 0 &*& mindex < i &*& m == a[mindex] &*& a |-> ?arr &*& array_slice(arr, 0, n, _);
      
      
      if (a[i] < m) {
        mindex = i;
        m = a[i];
      }
    }
    n--;
    a[mindex] = a[n];
    //@ close bag_pred();
    return m;
    
    
    
    
    

    
  }
  
}