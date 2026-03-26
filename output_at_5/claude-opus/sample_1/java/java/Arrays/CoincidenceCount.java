class CoincidenceCount {

/*@
  predicate array_int(int[] a, int length) =
    length == 0 ? true : a |-> ?data &*& data.length >= length &*& array_int(a, length - 1);
@*/

	public static int coincidenceCount(int[] xs, int[] ys)
	//@ requires xs != null &*& ys != null &*& xs.length >= 0 &*& ys.length >= 0 &*& xs.length == xs.length &*& ys.length == ys.length;
	//@ ensures true;
	{
		int i = 0;
		int j = 0;
		int n = 0;
		for (;;)
		//@ invariant 0 <= i &*& i <= xs.length &*& 0 <= j &*& j <= ys.length &*& n >= 0;
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