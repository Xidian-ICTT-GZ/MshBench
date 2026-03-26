/*@ predicate bag(Bag b; int[] values, int length) =
  b.a |-> ?arr &*&
  b.n |-> length &*&
  arr != null &*&
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
    //@ invariant 1 <= i &*& i <= n &*& bag(this, vals, len) &*& m == min_of_slice(vals, 0, i) &*& mindex >= 0 &*& mindex < i &*& vals[mindex] == m;
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

/*@ lemma void min_of_slice_def(int[] arr, int start, int end)
  requires start <= end &*& array_slice(arr, start, end, ?slice);
  ensures min_of_slice(slice, 0, end - start) == min_of_slice(arr, start, end);
@*/

/*@ lemma void min_preserved_after_swap(int[] arr, int len, int idx)
  requires 0 <= idx &*& idx < len &*& array_slice(arr, 0, len, ?vals) &*& len > 0;
  ensures array_slice(arr, 0, len - 1, ?newVals) &*& min(vals, len) == min(newVals, len - 1) || min(vals, len) == arr[len - 1];
@*/

/*@ predicate array_slice(int[] arr, int start, int end, int[] slice) =
  arr != null &*& start >= 0 &*& end >= start &*&
  foreach(slice, (i, v) => arr[start + i] == v) &*&
  length(slice) == end - start;
@*/

/*@ function int min(int[] arr, int len);
  requires len >= 0 &*& array_slice(?a, 0, len, arr);
  ensures true;
@*/

/*@ function int min_of_slice(int[] arr, int start, int end);
  requires start <= end &*& array_slice(?a, start, end, arr);
  ensures true;
@*/