class CoincidenceCount {

	//@ predicate xs_ys(int[] xs, int[] ys) = xs != null &*& ys != null &*& array_slice(xs, 0, xs.length, _) &*& array_slice(ys, 0, ys.length, _);
	//@ predicate xs_ys_perm(int[] xs, int[] ys, int i, int j) = xs != null &*& ys != null &*& 0 <= i &*& i <= xs.length &*& 0 <= j &*& j <= ys.length &*& array_slice(xs, i, xs.length, _) &*& array_slice(ys, j, ys.length, _);

	//@ requires xs_ys(xs, ys);
	//@ ensures xs_ys(xs, ys) &*& result >= 0;
	public static int coincidenceCount(int[] xs, int[] ys)
	
	
	{
		int i = 0;
		int j = 0;
		int n = 0;
		//@ close xs_ys_perm(xs, ys, i, j);
		for (;;)
		
		
		{
		    //@ open xs_ys_perm(xs, ys, i, j);
		    
			if (i == xs.length) {
				//@ close xs_ys_perm(xs, ys, i, j);
				break;
			}
			
		    
			if (j == ys.length) {
			    
				//@ close xs_ys_perm(xs, ys, i, j);
				break;
			}
			
    	    
		    //@ assert array_slice(xs, i, xs.length, ?xsVals);
		    //@ assert array_slice(ys, j, ys.length, ?ysVals);
		    //@ assert xsVals.length == xs.length - i;
		    //@ assert ysVals.length == ys.length - j;
		    //@ assert xsVals.length > 0;
		    //@ assert ysVals.length > 0;
		    
			if (xs[i] < ys[j]) {
			    
			    
				i++;
				//@ close xs_ys_perm(xs, ys, i, j);
			} else if (xs[i] > ys[j]) {
			    
				j++;
				//@ close xs_ys_perm(xs, ys, i, j);
			} else {
				n++;
				i++;
				j++;
				//@ close xs_ys_perm(xs, ys, i, j);

			}
		}
		//@ open xs_ys_perm(xs, ys, i, j);
		//@ close xs_ys(xs, ys);
		return n;
	}
}