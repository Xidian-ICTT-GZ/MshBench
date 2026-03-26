class CoincidenceCount {

    //@ predicate array(int[] arr;) = arr != null &*& arr.length |-> ?len &*& arr[0..len] |-> _;
    
    //@ requires array(xs) &*& array(ys);
    //@ ensures array(xs) &*& array(ys);
	public static int coincidenceCount(int[] xs, int[] ys)
	//@ requires xs != null &*& ys != null;
	//@ ensures true;
	{
		int i = 0;
		int j = 0;
		int n = 0;
		//@ close array(xs);
		//@ close array(ys);
		//@ int xs_len = xs.length;
		//@ int ys_len = ys.length;
		for (;;)
		//@ invariant 0 <= i &*& i <= xs_len &*& 0 <= j &*& j <= ys_len &*& 0 <= n;
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
		//@ open array(xs);
		//@ open array(ys);
		return n;
	}
}