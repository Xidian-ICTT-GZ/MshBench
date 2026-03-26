package tree;

/*@
predicate tree(Tree t; int min, int max, list<int> elems) =
  t == null ?
    elems == nil
  :
    t.value |-> ?v &
    t.left |-> ?l &
    t.right |-> ?r &
    v >= min &*& v <= max &
    chars_in_range(v) &*& // assume some character range predicate (optional)
    tree(l; min, v - 1, ?leftElems) &*&
    tree(r; v + 1, max, ?rightElems) &*&
    elems == append(leftElems, cons(v, rightElems)) &*&
    sorted(elems);
@*/

public class Tree{
	public int value;
	public Tree left;
	public Tree right;

	public Tree(int x)
	//@ requires true;
	//@ ensures value == x &*& left == null &*& right == null;
	{
	    	this.value=x;
		this.left=null;
		this.right=null;
	}
	public boolean contains(int x)
	//@ requires this != null &*& tree(this; _, _, ?elems);
	//@ ensures result == (exists(?y) == member(x, elems));
	{
		int v=this.value;
		Tree l=this.left;
		Tree r=this.right;
		if(v==x){
			return true;
		}else{
			if(x < v){
				boolean temp1=false;
				if(l != null) {
				  temp1 = l.contains(x);
				} else {
				}
				return temp1;
			}else{
				boolean temp2=false;
				if(r != null) {
				  temp2 = r.contains(x);
				} else {
				}
				return temp2;
			}
		}
	}
	public void add(int x)
	//@ requires this != null &*& tree(this; _, _, ?elems);
	//@ ensures tree(this; _, _, ?elems2) &*& elems2 == insert_sorted(x, elems);
	{
		int v=this.value;
		Tree l=this.left;
		Tree r=this.right;
		if(x < v){
			if(l!=null){
				l.add(x);
			}else{
				Tree temp=new Tree(x);
				this.left=temp;
			}
		}else{
			if(v < x){
				if(r!=null){
					r.add(x);
				}else{
					Tree temp=new Tree(x);
					this.right=temp;
				}
			}
		}
	}
	public int maximum()
	//@ requires this != null &*& tree(this; _, _, ?elems) &*& elems != nil;
	//@ ensures result == last(elems);
	{
		int v=this.value;
		Tree r=this.right;
		if(r==null){
			return v;
		}else{
			int m= r.maximum();
			return m;
		}
	}
	public Tree remove(int x)
	//@ requires this != null &*& tree(this; _, _, ?elems);
	//@ ensures (result == null ? true : tree(result; _, _, ?elems2)) &*& permutation(elems2, remove_one(x, elems));
	{
		int v=this.value;
		Tree l=this.left;
		Tree r=this.right;
		if(x < v){
			if(l!=null){
				Tree temp=l.remove(x);
				this.left=temp;
				return this;
			}
		}
		if(v < x){
			if(r!=null){
				Tree temp=r.remove(x);
				this.right=temp;
				return this;
			}
		}
		if(v==x){
			if(l!=null&&r==null){
				return l;
			}
			if(l==null&&r==null){
				return null;
			}
			if(l==null&&r!=null){
				return r;
			}
			if(l!=null&&r!=null){
				Tree temp=null;
				int m=l.maximum();
				this.value=m;
				temp=l.remove(m);
				this.left=temp;
				return this;
			}
		}
		return null; 
	}
	public static void main(String[]  args)
	//@ requires true;
	//@ ensures true;
	{
		Tree t1=null;
		Tree t2=null;
		Tree t3=null;
		boolean a=false;
		boolean b=false;
		boolean c=false;
		boolean d=false;
		boolean e=false;
		boolean f=false;

		t1 = new Tree(3);
		b=t1.contains(2);
		assert(!b);
		t1.add(2);

		a=t1.contains(2);
		assert(a);
		c=t1.contains(3);
		assert(c);
		t2=t1.remove(3);
		if(t2 != null) {
		  d= t2.contains(3);
		  assert(!d);

		  t2.add(3);
		  e= t2.contains(2);
		  assert(e);
		  t3=t2.remove(3);
		  if(t3 != null) {
		    f=t3.contains(3);
		    assert(!f);
		  }
		}
	}
}