class Bag {
  
  int[] a;
  int n;
  
  /*@
    predicate BagInstance(Bag this) = 
      a != null &*& 
      a.length > 0 &*& 
      0 <= n &*& n <= a.length &*& 
      arrayIsFilled(a, 0, n);
    
    predicate arrayIsFilled(int[] arr, int start, int end) = 
      start >= 0 &*& end >= 0 &*& start <= end &*& end <= arr.length &*&
      (forall int i; start <= i && i < end; true);
  @*/
  
  //@ requires true;
  //@ ensures BagInstance(this);
  Bag(int[] input)
    
    
  {
    n = input.length;
    a = new int[n];

    
    
    
    
    System.arraycopy(input, 0, a, 0, n);
    
    
  }
  
  //@ requires BagInstance(this) &*& n > 0;
  //@ ensures BagInstance(this) &*& result == old(a[mindex]);
  int extractMin()
    
    

  {
    int mindex = 0;
    
    int m = a[mindex];
    for (int i = 1; i < n; i++)
      

    {
      //@ loop invariant 0 <= mindex &*& mindex < i &*& mindex < n;
      //@ loop invariant 0 <= i &*& i <= n;
      //@ loop invariant 0 <= mindex &*& mindex < n;
      //@ loop invariant m == min(a, 0, i);
      //@ loop invariant BagInstance(this);
      
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