class CoincidenceCount {

/*@
predicate arrays(int[] xs, int[] ys, list<int> xsElems, list<int> ysElems) =
    array_slice(xs, 0, xs.length, xsElems) &*& array_slice(ys, 0, ys.length, ysElems);
@*/

	public static int coincidenceCount(int[] xs, int[] ys)
	//@ requires xs != null &*& ys != null &*& xs.length >= 0 &*& ys.length >= 0 &*& array_slice(xs, 0, xs.length, ?xsElems) &*& array_slice(ys, 0, ys.length, ?ysElems);
	//@ ensures result >= 0;
	{
		int i = 0;
		int j = 0;
		int n = 0;
		//@ list<int> lxs = xsElems;
		//@ list<int> lys = ysElems;
		for (;;)
		//@ invariant 0 <= i &*& i <= xs.length &*& 0 <= j &*& j <= ys.length &*& n >= 0 &*& array_slice(xs, 0, xs.length, lxs) &*& array_slice(ys, 0, ys.length, lys);
		//@ decreases xs.length - i + ys.length - j;
		{
			if (i == xs.length) {
				break;
			}
			if (j == ys.length) {
				break;
			}
			if (xs[i] < ys[j]) {
				//@ lxs = tail(lxs);
				i++;
			} else if (xs[i] > ys[j]) {
				//@ lys = tail(lys);
				j++;
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