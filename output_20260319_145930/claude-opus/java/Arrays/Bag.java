/*@
predicate BagInv(Bag b; int[] arr, int len) =
    b.a |-> arr &*& b.n |-> len &*&
    arr != null &*& array_slice(arr, 0, arr.length, _) &*&
    0 <= len &*& len <= arr.length;
@*/

class Bag {
  
  int[] a;
  int n;
  
  
  
  Bag(int[] input)
    //@ requires input != null &*& array_slice(input, 0, input.length, _);
    //@ ensures BagInv(this, _, input.length) &*& array_slice(input, 0, input.length, _);
  {
    n = input.length;
    a = new int[n];

    
    
    
    
    System.arraycopy(input, 0, a, 0, n);
    //@ close BagInv(this, a, n);
    
    
  }
  
  int extractMin()
    //@ requires BagInv(this, ?arr, ?len) &*& len > 0;
    //@ ensures BagInv(this, arr, len - 1);
  {
    //@ open BagInv(this, arr, len);
    int mindex = 0;
    
    int m = a[mindex];
    for (int i = 1; i < n; i++)
      //@ invariant array_slice(a, 0, a.length, _) &*& 0 <= mindex &*& mindex < n &*& 1 <= i &*& i <= n &*& n == len &*& a == arr;
    {
      
      
      if (a[i] < m) {
        mindex = i;
        m = a[i];
      }
    }
    n--;
    a[mindex] = a[n];
    //@ close BagInv(this, a, n);
    return m;
    
    
    
    
    

    
  }
  
}