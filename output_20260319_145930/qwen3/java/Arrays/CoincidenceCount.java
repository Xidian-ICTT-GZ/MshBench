class CoincidenceCount {

	/*@ predicate array(int[] a; int l) = [_]a |-> ?contents &*& l == contents.length; @*/

	public static int coincidenceCount(int[] xs, int[] ys)
	//@ requires array(xs, ?lenXs) &*& array(ys, ?lenYs);
	//@ ensures true;
	{
		int i = 0;
		int j = 0;
		int n = 0;
		//@ open array(xs, lenXs);
		//@ open array(ys, lenYs);
		//@ close array(xs, lenXs);
		//@ close array(ys, lenYs);
		for (;;)
		//@ invariant array(xs, lenXs) &*& array(ys, lenYs) &*& 0 <= i &*& i <= lenXs &*& 0 <= j &*& j <= lenYs &*& 0 <= n;
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