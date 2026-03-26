class CoincidenceCount {

	public static int coincidenceCount(int[] xs, int[] ys)
	//@ requires xs != null &*& ys != null &*& 0 <= xs.length &*& 0 <= ys.length &*& array_slice(xs, 0, xs.length, ?xsElems) &*& array_slice(ys, 0, ys.length, ?ysElems);
	//@ ensures result >= 0 &*& result <= xs.length &*& array_slice(xs, 0, xs.length, xsElems) &*& array_slice(ys, 0, ys.length, ysElems);
	{
		int i = 0;
		int j = 0;
		int n = 0;
		//@ list<int> lxs = xsElems;
		//@ list<int> lys = ysElems;
		for (;;)
		//@ invariant 0 <= i &*& i <= xs.length &*& 0 <= j &*& j <= ys.length &*& 0 <= n &*& n <= i &*& n <= j &*& array_slice(xs, 0, xs.length, xsElems) &*& array_slice(ys, 0, ys.length, ysElems);
		//@ decreases xs.length - i + ys.length - j;
		{
			if (i == xs.length) {
				break;
			}
			if (j == ys.length) {
				break;
			}
			if (xs[i] < ys[j]) {
				i++;
				//@ lxs = tail(lxs);
			} else if (xs[i] > ys[j]) {
				j++;
				//@ lys = tail(lys);
			} else {
				n++;
				i++;
				j++;
				//@ lxs = tail(lxs);
				//@ lys = tail(lys);
			}
		}
		return n;
	}
}