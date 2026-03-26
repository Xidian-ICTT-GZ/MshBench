class Bag {
  
  int[] a;
  int n;
  
  /*@
  predicate Bag(Bag b; int[] arr, int len) =
    b.a |-> arr &*& b.n |-> len &*&
    arr != null &*&
    array_slice(arr, 0, len, _);
  @*/
  
  Bag(int[] input)
  //@ requires input != null &*& array_slice(input, 0, input.length, _);
  //@ ensures Bag(this, result_a, result_n) &*& result_a != null &*& result_n == input.length;
  {
    n = input.length;
    a = new int[n];
    //@ close array_slice(a, 0, n, _);
    //@ open array_slice(a, 0, n, _);
    
    System.arraycopy(input, 0, a, 0, n);
    
    //@ close Bag(this, a, n);
  }
  
  int extractMin()
  //@ requires Bag(this, ?arr, ?len) &*& len > 0;
  //@ ensures Bag(this, arr, len - 1) &*& result == minimum_of_slice(arr, 0, len);
  {
    //@ open Bag(this, arr, len);
    //@ assert arr != null;
    //@ assert array_slice(arr, 0, len, _);
    
    int mindex = 0;
    int m = a[mindex];
    
    //@ int i = 1;
    //@ loop_invariant 1 <= i &*& i <= len &*&
    //@   m == minimum_of_slice(arr, 0, i) &*&
    //@   mindex >= 0 &*& mindex < i &*&
    //@   arr[mindex] == m &*&
    //@   array_slice(arr, 0, len, _);
    for (int i = 1; i < n; i++)
    {
      if (a[i] < m) {
        mindex = i;
        m = a[i];
      }
      //@ i++;
    }
    
    n--;
    a[mindex] = a[n];
    
    //@ close Bag(this, arr, n);
    return m;
  }
  
}