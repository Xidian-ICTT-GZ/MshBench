class CoincidenceCount {

	public static int coincidenceCount(int[] xs, int[] ys)
	//@ requires xs != null &*& ys != null &*& xs.length >= 0 &*& ys.length >= 0 &*& array_slice(xs, 0, xs.length, ?xsElems) &*& array_slice(ys, 0, ys.length, ?ysElems);
	//@ ensures true;
	{
		int i = 0;
		int j = 0;
		int n = 0;
		for (;;)
		//@ invariant 0 <= i &*& i <= xs.length &*& 0 <= j &*& j <= ys.length &*& n >= 0 &*& array_slice(xs, 0, xs.length, ?xsElems) &*& array_slice(ys, 0, ys.length, ?ysElems);
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