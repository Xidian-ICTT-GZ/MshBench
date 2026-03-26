class CoincidenceCount {

	//@ requires xs != null &*& ys != null;
	//@ requires xs.length >= 0 &*& ys.length >= 0;
	//@ requires array_slice(xs, 0, xs.length, _);
	//@ requires array_slice(ys, 0, ys.length, _);
	//@ ensures array_slice(xs, 0, xs.length, _);
	//@ ensures array_slice(ys, 0, ys.length, _);
	//@ ensures result >= 0;
	public static int coincidenceCount(int[] xs, int[] ys)
	{
		int i = 0;
		int j = 0;
		int n = 0;
		for (;;)
		//@ invariant xs != null &*& ys != null;
		//@ invariant array_slice(xs, 0, xs.length, _) &*& array_slice(ys, 0, ys.length, _);
		//@ invariant 0 <= i &*& i <= xs.length;
		//@ invariant 0 <= j &*& j <= ys.length;
		//@ invariant n >= 0;
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