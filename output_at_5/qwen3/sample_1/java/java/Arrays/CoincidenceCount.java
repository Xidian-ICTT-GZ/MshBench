class CoincidenceCount {

	//@ requires xs != null && ys != null;
	//@ ensures \result == \old(coincidenceCount(xs, ys));
	public static int coincidenceCount(int[] xs, int[] ys)
	
	
	{
		int i = 0;
		int j = 0;
		int n = 0;
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
		return n;
	}
}