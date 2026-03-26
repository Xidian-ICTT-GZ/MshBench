class CoincidenceCount {

	public static int coincidenceCount(int[] xs, int[] ys)
	//@ requires xs != null &*& ys != null;
	//@ ensures true;
	
	
	{
		int i = 0;
		int j = 0;
		int n = 0;
		for (;;)
		//@ invariant xs != null &*& ys != null &*& 0 <= i &*& 0 <= j;
		
		
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