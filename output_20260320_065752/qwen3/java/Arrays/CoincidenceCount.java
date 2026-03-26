class CoincidenceCount {

	/*@
	predicate array_range(int[] a, int min, int max) =
		a != null &*&
		a.length >= 0 &*&
		min <= max &*&
		0 <= min &*&
		max <= a.length;
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