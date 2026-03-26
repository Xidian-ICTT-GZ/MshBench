/*@ predicate array_slice(int[] a, int start, int end; int[] values) =
    start >= 0 &*& end >= start &*& a != null &*& a.length >= end &*&
    forall(start, end, (int i) => a[i] == values[i - start]); @*/

/*@ predicate sorted_array(int[] a) =
    a != null &*&
    forall(0, a.length - 1, (int i) => a[i] <= a[i + 1]); @*/

class CoincidenceCount {

	//@ requires xs != null &*& ys != null &*& sorted_array(xs) &*& sorted_array(ys);
	//@ ensures result >= 0;
	public static int coincidenceCount(int[] xs, int[] ys)
	{
		int i = 0;
		int j = 0;
		int n = 0;
		//@ loop_invariant i >= 0 &*& j >= 0 &*& n >= 0 &*& i <= xs.length &*& j <= ys.length &*&
		//@   sorted_array(xs) &*& sorted_array(ys) &*&
		//@   forall(0, i, (int k) => exists(0, j, (int l) => xs[k] == ys[l])) ==>
		//@     n >= count_coincidences_up_to(xs, ys, i, j);
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

	/*@ lemma void count_coincidences_up_to_lemma()
	    requires true;
	    ensures true;
	@*/
	{
	}
}