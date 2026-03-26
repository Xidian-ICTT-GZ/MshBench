package tree;

/*@
predicate tree(Tree t) =
  t == null ? true :
  t.value |-> _ &*& t.left |-> ?l &*& t.right |-> ?r &*& tree(l) &*& tree(r);
@*/

public class Tree {
	public int value;
	public Tree left;
	public Tree right;

	public Tree(int x)
	//@ requires true;
	//@ ensures tree(this);
	{
		this.value = x;
		this.left = null;
		this.right = null;
		//@ close tree(this);
	}

	public boolean contains(int x)
	//@ requires tree(this);
	//@ ensures tree(this);
	{
		//@ open tree(this);
		int v = this.value;
		Tree l = this.left;
		Tree r = this.right;
		if (v == x) {
			//@ close tree(this);
			return true;
		} else {
			if (x < v) {
				boolean temp1 = false;
				if (l != null) {
					//@ open tree(l);
					temp1 = l.contains(x);
					//@ close tree(l);
				}
				//@ close tree(this);
				return temp1;
			} else {
				boolean temp2 = false;
				if (r != null) {
					//@ open tree(r);
					temp2 = r.contains(x);
					//@ close tree(r);
				}
				//@ close tree(this);
				return temp2;
			}
		}
	}

	public void add(int x)
	//@ requires tree(this);
	//@ ensures tree(this);
	{
		//@ open tree(this);
		int v = this.value;
		Tree l = this.left;
		Tree r = this.right;

		if (x < v) {
			if (l != null) {
				//@ open tree(l);
				l.add(x);
				//@ close tree(l);
			} else {
				Tree temp = new Tree(x);
				this.left = temp;
			}
		} else {
			if (v < x) {
				if (r != null) {
					//@ open tree(r);
					r.add(x);
					//@ close tree(r);
				} else {
					Tree temp = new Tree(x);
					this.right = temp;
				}
			}
		}
		//@ close tree(this);
	}

	public int maximum()
	//@ requires tree(this);
	//@ ensures tree(this);
	{
		//@ open tree(this);
		int v = this.value;
		Tree r = this.right;

		if (r == null) {
			//@ close tree(this);
			return v;
		} else {
			//@ open tree(r);
			int m = r.maximum();
			//@ close tree(r);
			//@ close tree(this);
			return m;
		}
	}

	public Tree remove(int x)
	//@ requires tree(this);
	//@ ensures true;
	{
		//@ open tree(this);
		int v = this.value;
		Tree l = this.left;
		Tree r = this.right;

		if (x < v) {
			if (l != null) {
				//@ open tree(l);
				Tree temp = l.remove(x);
				this.left = temp;
				//@ close tree(this);
				return this;
			}
		}
		if (v < x) {
			if (r != null) {
				//@ open tree(r);
				Tree temp = r.remove(x);
				this.right = temp;
				//@ close tree(this);
				return this;
			}
		}
		if (v == x) {
			if (l != null && r == null) {
				//@ close tree(this);
				return l;
			}
			if (l == null && r == null) {
				//@ close tree(this);
				return null;
			}
			if (l == null && r != null) {
				//@ close tree(this);
				return r;
			}
			if (l != null && r != null) {
				//@ open tree(l);
				Tree temp = null;
				int m = l.maximum();
				this.value = m;
				temp = l.remove(m);
				this.left = temp;
				//@ close tree(l);
				//@ close tree(this);
				return this;
			}
		}
		//@ close tree(this);
		return null;
	}

	public static void main(String[] args)
	//@ requires true;
	//@ ensures true;
	{
		Tree t1 = null;
		Tree t2 = null;
		Tree t3 = null;
		boolean a = false;
		boolean b = false;
		boolean c = false;
		boolean d = false;
		boolean e = false;
		boolean f = false;

		t1 = new Tree(3);
		b = t1.contains(2);
		assert (!b);
		t1.add(2);

		a = t1.contains(2);
		assert (a);
		c = t1.contains(3);
		assert (c);
		t2 = t1.remove(3);
		if (t2 != null) {
			d = t2.contains(3);
			assert (!d);

			t2.add(3);
			e = t2.contains(2);
			assert (e);
			t3 = t2.remove(3);
			if (t3 != null) {
				f = t3.contains(3);
				assert (!f);
			}
		}
	}
}