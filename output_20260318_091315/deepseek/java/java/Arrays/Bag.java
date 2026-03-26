class Bag {
  
  int[] a;
  int n;
  
  //@ predicate Bag(int[] input) = a |-> ?aArray &*& n |-> ?nVal &*& aArray != null &*& array_slice(aArray, 0, nVal, _) &*& nVal == input.length &*& array_slice(input, 0, nVal, _);
  
  Bag(int[] input)
    //@ requires array_slice(input, 0, input.length, _);
    //@ ensures Bag(input);
  {
    n = input.length;
    a = new int[n];
    //@ close array_slice(a, 0, n, _);
    System.arraycopy(input, 0, a, 0, n);
    //@ close Bag(input);
  }
  
  int extractMin()
    //@ requires Bag(?input) &*& n > 0;
    //@ ensures Bag(input) &*& result <= old(m) &*& true;
  {
    int mindex = 0;
    //@ open Bag(input);
    int m = a[mindex];
    //@ int i = 1;
    //@ close loop_inv(0, mindex, m, i);
    for (int i = 1; i < n; i++)
      //@ invariant loop_inv(0, mindex, m, i) &*& i <= n;
      //@ decreases n - i;
    {
      //@ open loop_inv(_, _, _, _);
      if (a[i] < m) {
        mindex = i;
        m = a[i];
      }
      //@ close loop_inv(0, mindex, m, i+1);
    }
    //@ open loop_inv(_, _, _, _);
    n--;
    a[mindex] = a[n];
    //@ close Bag(input);
    return m;
  }
  
  //@ predicate loop_inv(int start, int mindex, int m, int i) = a |-> ?aArray &*& n |-> ?nVal &*& aArray != null &*& array_slice(aArray, 0, nVal, _) &*& start <= mindex &*& mindex < i &*& m == aArray[mindex] &*& forall(start, i, (leq)(aArray, m)) == true;
  
  //@ predicate_ctor leq(int[] arr, int val)(int index) = arr[index] >= val;
  
  //@ lemma void forall_append(int[] arr, int val, int from, int mid, int to)
  //@ requires forall(from, mid, (leq)(arr, val)) == true &*& forall(mid, to, (leq)(arr, val)) == true;
  //@ ensures forall(from, to, (leq)(arr, val)) == true;
  {}
  
}