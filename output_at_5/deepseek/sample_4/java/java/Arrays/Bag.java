class Bag {
  
  int[] a;
  int n;
  
  /*@
  predicate Bag(int[] arr, int size) = a |-> arr &*& n |-> size &*& arr != null &*& 0 <= size &*& size <= arr.length &*& array_slice(arr, 0, size, _);
  @*/
  
  Bag(int[] input)
    //@ requires input != null;
    //@ ensures Bag(a, n);
  {
    n = input.length;
    a = new int[n];
    //@ close array_slice(a, 0, n, _);
    //@ close Bag(a, n);
    System.arraycopy(input, 0, a, 0, n);
  }
  
  int extractMin()
    //@ requires Bag(a, n) &*& n > 0;
    //@ ensures Bag(a, n);
  {
    //@ open Bag(a, n);
    int mindex = 0;
    int m = a[mindex];
    //@ assert array_slice(a, 0, n, _);
    for (int i = 1; i < n; i++)
      //@ invariant 1 <= i && i <= n;
      //@ invariant 0 <= mindex && mindex < n;
      //@ invariant m == a[mindex];
      //@ invariant array_slice(a, 0, n, _);
    {
      if (a[i] < m) {
        mindex = i;
        m = a[i];
      }
    }
    n--;
    a[mindex] = a[n];
    //@ close array_slice(a, 0, n, _);
    //@ close Bag(a, n);
    return m;
  }
  
}