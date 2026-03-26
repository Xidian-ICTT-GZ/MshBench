class Bag {
  
  int[] a;
  int n;
  
  //@ predicate Bag(int[] arr, int size) = a |-> arr &*& n |-> size &*& arr != null &*& 0 <= size &*& size <= arr.length &*& array_slice(arr, 0, size, _);
  
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
    //@ ensures Bag(a, n) &*& result == old(m) &*& n == old(n) - 1;
  {
    //@ open Bag(a, n);
    int mindex = 0;
    int m = a[mindex];
    //@ assert array_slice(a, 0, n, _);
    //@ int i = 1;
    //@ close [f]array_slice(a, 0, n, _);
    for (int i = 1; i < n; i++)
      //@ invariant 1 <= i &*& i <= n &*& [f]array_slice(a, 0, n, _) &*& mindex >= 0 &*& mindex < n;
      //@ decreases n - i;
    {
      //@ open [f]array_slice(a, 0, n, _);
      //@ close [f]array_slice(a, 0, n, _);
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