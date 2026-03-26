/*@ predicate bag(Bag b; int[] values, int length) =
  b.a |-> ?arr &*& b.n |-> length &*&
  array_slice(arr, 0, length, values) &*&
  length >= 0;
@*/

class Bag {
  
  int[] a;
  int n;
  
  
  
  //@ requires input != null &*& array_slice(input, 0, ?len, ?vals) &*& len >= 0;
  //@ ensures bag(this, vals, len);
  Bag(int[] input)
  {
    n = input.length;
    a = new int[n];

    System.arraycopy(input, 0, a, 0, n);
  }
  
  //@ requires bag(this, ?vals, ?len) &*& len > 0;
  //@ ensures bag(this, ?newVals, len - 1) &*& result == min(vals, len);
  int extractMin()
  {
    int mindex = 0;
    
    int m = a[mindex];
    for (int i = 1; i < n; i++)
    //@ invariant 1 <= i &*& i <= n &*& bag(this, vals, len) &*& m == min_prefix(vals, i) &*& mindex >= 0 &*& mindex < i &*& a[mindex] == m;
    {
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

/*@ lemma void min_prefix_def(int[] arr, int i)
  requires i >= 1 &*& array_slice(arr, 0, i, ?vals);
  ensures min_prefix(vals, i) == minimum_of_slice(arr, 0, i);
@*/

/*@ lemma void min_def(int[] arr, int len)
  requires len > 0 &*& array_slice(arr, 0, len, ?vals);
  ensures min(vals, len) == minimum_of_slice(arr, 0, len);
@*/