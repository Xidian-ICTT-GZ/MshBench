class CoincidenceCount {

	//@ predicate sorted(int[] arr) = arr != null &*& arr.length >= 0 &*& array_slice(arr, 0, arr.length, _);
	//@ predicate sorted_slice(int[] arr, int from, int to) = arr != null &*& 0 <= from &*& from <= to &*& to <= arr.length &*& array_slice(arr, from, to, _);

	public static int coincidenceCount(int[] xs, int[] ys)
	//@ requires sorted(xs) &*& sorted(ys);
	//@ ensures sorted(xs) &*& sorted(ys);
	{
		int i = 0;
		int j = 0;
		int n = 0;
		//@ split_array_slice(xs);
		//@ split_array_slice(ys);
		//@ assert sorted_slice(xs, 0, xs.length);
		//@ assert sorted_slice(ys, 0, ys.length);
		for (;;)
		//@ invariant 0 <= i &*& i <= xs.length &*& sorted_slice(xs, i, xs.length) &*& 0 <= j &*& j <= ys.length &*& sorted_slice(ys, j, ys.length) &*& n >= 0;
		{
		    
			if (i == xs.length) {
				//@ merge_array_slice(xs);
				break;
			}
			
		    
			if (j == ys.length) {
			    
				//@ merge_array_slice(ys);
				break;
			}
			
    	    
		    //@ assert i < xs.length;
		    //@ assert j < ys.length;
			if (xs[i] < ys[j]) {
			    
			    
				i++;
				//@ split_array_slice(xs);
			} else if (xs[i] > ys[j]) {
			    
				j++;
				//@ split_array_slice(ys);
			} else {
				n++;
				i++;
				j++;
				//@ split_array_slice(xs);
				//@ split_array_slice(ys);

			}
		}
		//@ merge_array_slice(xs);
		//@ merge_array_slice(ys);
		return n;
	}
}