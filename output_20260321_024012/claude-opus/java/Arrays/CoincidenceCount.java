class CoincidenceCount {

/*@
  predicate array_int(int[] a, int lo, int hi;) =
    lo == hi ? emp :
    lo < hi &*& a[lo] |-> _ &*& array_int(a, lo + 1, hi);
@*/

	public static int coincidenceCount(int[] xs, int[] ys)
	//@ requires xs != null &*& ys != null &*& array_int(xs, 0, xs.length) &*& array_int(ys, 0, ys.length);
	//@ ensures array_int(xs, 0, xs.length) &*& array_int(ys, 0, ys.length) &*& 0 <= result;
	{
		int i = 0;
		int j = 0;
		int n = 0;
		for (;;)
		//@ invariant 0 <= i &*& i <= xs.length &*& 0 <= j &*& j <= ys.length &*& 0 <= n;
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