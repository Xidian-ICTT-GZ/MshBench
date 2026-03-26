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
    //@ open array_slice(a, 0, n, _);
    //@ close array_slice(a, 0, n, _);
  }
  
  int extractMin()
    //@ requires Bag(a, n) &*& n > 0;
    //@ ensures Bag(a, n-1);
  {
    //@ open Bag(a, n);
    int mindex = 0;
    
    int m = a[mindex];
    //@ assert array_slice(a, 0, n, _);
    //@ int i = 1;
    //@ close [f]array_slice(a, 0, n, _);
    //@ close foreach(0, n, isMin(mindex, m));
    for (int i = 1; i < n; i++)
      //@ invariant 1 <= i &*& i <= n &*& [f]array_slice(a, 0, n, _) &*& foreach(i, n, isMin(mindex, m));
      //@ decreases n - i;
    {
      //@ open foreach(i, n, isMin(mindex, m));
      //@ assert isMin(mindex, m)(i-1);
      //@ open isMin(mindex, m)(i-1);
      
      if (a[i] < m) {
        mindex = i;
        m = a[i];
      }
      //@ close isMin(mindex, m)(i);
      //@ close foreach(i+1, n, isMin(mindex, m));
    }
    //@ open foreach(n, n, isMin(mindex, m));
    //@ open [f]array_slice(a, 0, n, _);
    n--;
    a[mindex] = a[n];
    //@ close array_slice(a, 0, n, _);
    //@ close Bag(a, n);
    return m;
  }
  
  //@ predicate isMin(int idx, int val)(int i) = [1/2]array_slice(a, i, i+1, _) &*& a[i] >= val;
  
}