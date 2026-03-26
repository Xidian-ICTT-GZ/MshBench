class CoincidenceCount {

	/*@ 
	predicate array_range(int[] a, int start, int end) =
		start <= end &*&
		a != null &*&
		a.length >= end &*&
		foreach(start, end, ?f) &*&
		forall(start, end, (i => [1/2]a[i] |-> _));
	@*/

	public static int coincidenceCount(int[] xs, int[] ys)
	//@ requires array_range(xs, 0, xs.length) &*& array_range(ys, 0, ys.length);
	//@ ensures true;
	{
		int i = 0;
		int j = 0;
		int n = 0;
		//@ open array_range(xs, 0, xs.length);
		//@ open array_range(ys, 0, ys.length);
		//@ close array_range(xs, 0, xs.length);
		//@ close array_range(ys, 0, ys.length);
		for (;;)
		//@ invariant 0 <= i &*& i <= xs.length &*& 0 <= j &*& j <= ys.length &*& 0 <= n;
		//@ invariant array_range(xs, 0, xs.length) &*& array_range(ys, 0, ys.length);
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