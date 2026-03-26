class CoincidenceCount {

	//@ requires xs != null;
	//@ requires ys != null;
	//@ ensures \result >= 0;
	public static int coincidenceCount(int[] xs, int[] ys)
	
	
	{
		int i = 0;
		int j = 0;
		int n = 0;
		//@ loop_invariant 0 <= i && i <= xs.length;
		//@ loop_invariant 0 <= j && j <= ys.length;
		//@ loop_invariant 0 <= n;
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
		//@ assert 0 <= n;
		return n;
	}
}