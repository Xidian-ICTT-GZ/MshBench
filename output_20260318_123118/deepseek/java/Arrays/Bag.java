class Bag {
  
  int[] a;
  int n;
  
  //@ predicate Bag(int[] input) = a |-> ?arr &*& arr != null &*& arr.length == n &*& n == input.length &*& array_slice(arr, 0, n, _);
  
  Bag(int[] input)
    //@ requires input != null;
    //@ ensures Bag(input);
  {
    n = input.length;
    a = new int[n];
    //@ close array_slice(a, 0, n, _);
    System.arraycopy(input, 0, a, 0, n);
    //@ close Bag(input);
  }
  
  int extractMin()
    //@ requires Bag(?in) &*& n > 0;
    //@ ensures Bag(in) &*& result <= old(m) &*& old(m) == result;
  {
    int mindex = 0;
    //@ assert a != null;
    //@ open array_slice(a, 0, n, _);
    int m = a[mindex];
    //@ int i = 1;
    //@ close array_slice(a, 0, n, _);
    //@ close foreach(0, n, a);
    for (int i = 1; i < n; i++)
      //@ invariant 1 <= i &*& i <= n &*& foreach(0, n, a) &*& m == a[mindex] &*& 0 <= mindex &*& mindex < n;
      //@ decreases n - i;
    {
      //@ open foreach(0, n, a);
      //@ open array_slice(a, 0, n, _);
      if (a[i] < m) {
        mindex = i;
        m = a[i];
      }
      //@ close array_slice(a, 0, n, _);
      //@ close foreach(0, n, a);
    }
    //@ open foreach(0, n, a);
    n--;
    //@ open array_slice(a, 0, n+1, _);
    a[mindex] = a[n];
    //@ close array_slice(a, 0, n, _);
    //@ close Bag(in);
    return m;
  }
  
}