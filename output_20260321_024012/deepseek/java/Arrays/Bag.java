class Bag {
  
  int[] a;
  int n;
  
  //@ predicate Bag(int[] arr, int sz) = a |-> arr &*& n |-> sz &*& arr != null &*& 0 <= sz &*& sz <= arr.length &*& array_slice(arr, 0, sz, _);
  
  Bag(int[] input)
  //@ requires input != null;
  //@ ensures Bag(input, input.length);
  {
    n = input.length;
    a = new int[n];
    //@ close array_slice(a, 0, n, _);
    System.arraycopy(input, 0, a, 0, n);
    //@ close Bag(a, n);
  }
  
  int extractMin()
  //@ requires Bag(a, n) &*& n > 0;
  //@ ensures Bag(a, n-1) &*& result == old(m) &*& 0 <= old(mindex) &*& old(mindex) < old(n);
  {
    //@ open Bag(a, n);
    int mindex = 0;
    int m = a[mindex];
    //@ assert 0 <= mindex && mindex < n;
    //@ int i = 1;
    //@ close foreach(0, 0, _);
    //@ close foreach(0, 1, _);
    for (int i = 1; i < n; i++)
    //@ invariant 1 <= i && i <= n &*& foreach(0, i, _) &*& 0 <= mindex &*& mindex < n &*& m == a[mindex];
    {
      //@ open foreach(0, i, _);
      //@ assert 0 <= i && i < n;
      if (a[i] < m) {
        mindex = i;
        m = a[i];
      }
      //@ close foreach(0, i+1, _);
    }
    //@ open foreach(0, n, _);
    n--;
    a[mindex] = a[n];
    //@ close array_slice(a, 0, n, _);
    //@ close Bag(a, n);
    return m;
  }
  
}