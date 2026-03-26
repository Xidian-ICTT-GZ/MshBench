class CoincidenceCount {

	/*@ 
	predicate array_slice(int[] a, int start, int end) = 
		start <= end &*& 
		a != null &*& 
		a.length >= end &*& 
		foreach(a, ?elems) &*& 
		true;
	@*/

	public static int coincidenceCount(int[] xs, int[] ys)
	//@ requires array_slice(xs, 0, xs.length) &*& array_slice(ys, 0, ys.length);
	//@ ensures true;
	{
		int i = 0;
		int j = 0;
		int n = 0;
		//@ open array_slice(xs, 0, xs.length);
		//@ open array_slice(ys, 0, ys.length);
		for (;;)
		//@ invariant 0 <= i &*& i <= xs.length &*& 0 <= j &*& j <= ys.length &*& array_slice(xs, i, xs.length) &*& array_slice(ys, j, ys.length);
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
		//@ close array_slice(xs, i, xs.length);
		//@ close array_slice(ys, j, ys.length);
		return n;
	}
}