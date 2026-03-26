class Bag {
  
  int[] a;
  int n;
  
  //@ predicate Bag(int[] arr, int sz) = a |-> arr &*& n |-> sz &*& arr != null &*& 0 <= sz &*& sz <= arr.length &*& array_slice(arr, 0, sz, _);
  
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
  //@ ensures Bag(a, n-1) &*& result == old_m;
  {
    //@ open Bag(a, n);
    int mindex = 0;
    int m = a[mindex];
    //@ int old_m = m;
    //@ int i = 1;
    //@ close foreach(0, 0, _);
    //@ close foreach(0, 1, _);
    for (int i = 1; i < n; i++)
    //@ invariant 1 <= i &*& i <= n &*& a |-> ?arr &*& n |-> ?sz &*& arr != null &*& 0 <= sz &*& sz <= arr.length &*& array_slice(arr, 0, sz, _) &*& 0 <= mindex &*& mindex < sz &*& m == arr[mindex];
    {
      if (a[i] < m) {
        mindex = i;
        m = a[i];
      }
    }
    n--;
    a[mindex] = a[n];
    //@ close Bag(a, n);
    return m;
  }
  
}