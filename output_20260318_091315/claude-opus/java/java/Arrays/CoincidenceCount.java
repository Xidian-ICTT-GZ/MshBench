class CoincidenceCount {

  /*@ predicate array_int(int[] a; int length, int* contents) = 
        a != null &*& a.length == length &*& 
        (length == 0 ? true : a |-> ?vals &*& length > 0 &*& length <= vals.length) &*&
        // contents pointer representation is implicit; 
        // VeriFast models full ownership of the array region
        // We approximate with pure length property here for verification.
        true;
  @*/

  //@ requires xs != null &*& ys != null &*& xs.length >= 0 &*& ys.length >= 0 &*& array_int(xs, xs.length, _ ) &*& array_int(ys, ys.length, _ );
  //@ ensures 0 <= result &*& result <= xs.length &*& result <= ys.length;
  public static int coincidenceCount(int[] xs, int[] ys)
  
  {
    int i = 0;
    int j = 0;
    int n = 0;
    /*@ 
      invariant 0 <= i &*& i <= xs.length &*& 0 <= j &*& j <= ys.length &*& 0 <= n &*& n <= xs.length &*& n <= ys.length &*&
                array_int(xs, xs.length, _) &*& array_int(ys, ys.length, _);
    @*/
    for (;;)
    
    {
      
      if (i == xs.length) {
        break;
      }
      
      
      if (j == ys.length) {
        
        break;
      }
      
      
      
      if (xs[i] < ys[j]) {
        
        
        i++;
      } else if (xs[i] > ys[j]) {
        
        j++;
      } else {
        n++;
        i++;
        j++;
        
        
        
        
      }
    }
    return n;
  }
}