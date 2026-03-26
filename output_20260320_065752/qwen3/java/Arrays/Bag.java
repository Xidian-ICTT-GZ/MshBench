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
    //@ close Bag(this, a, n);
    
    System.arraycopy(input, 0, a, 0, n);
  }
  
  int extractMin()
  //@ requires Bag(this, ?arr, ?len) &*& len > 0;
  //@ ensures Bag(this, arr, len - 1) &*& result == arr[?i] &*& i >= 0 &*& i < len;
  {
    //@ open Bag(this, _, _);
    int mindex = 0;
    
    int m = a[mindex];
    for (int i = 1; i < n; i++)
    //@ invariant 1 <= i &*& i <= n &*& mindex >= 0 &*& mindex < i &*& m == a[mindex] &*& Bag(this, ?arr, ?len) &*& len == n;
    {
      if (a[i] < m) {
        mindex = i;
        m = a[i];
      }
    }
    n--;
    a[mindex] = a[n];
    //@ close Bag(this, a, n);
    return m;
  }
  
}