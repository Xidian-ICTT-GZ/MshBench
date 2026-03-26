package tree;

/*@
predicate tree(Tree t) = 
  t == null ? true : t.value |-> _ &*& t.left |-> ?l &*& t.right |-> ?r &*& tree(l) &*& tree(r);
@*/

public class Tree {
	public int value;
	public Tree left;
	public Tree right;

	//@ requires true;
	//@ ensures tree(this);
	public Tree(int x)
	{
	    	this.value=x;
		this.left=null;
		this.right=null;
	}

	//@ requires tree(this);
	//@ ensures tree(this) &*& result == (this.value == x || (this.left != null && this.left.contains(x)) || (this.right != null && this.right.contains(x)));
	public boolean contains(int x)
	{
		//@ open tree(this);
		int v=this.value;
		Tree l=this.left;
		Tree r=this.right;
		if(v==x){
			//@ close tree(this);
			return true;
		}else{
			if(x < v){
				boolean temp1=false;
				if(l != null) {
				  //@ assert l != null;
				  temp1 = l.contains(x);
				} else {
					
				}
				//@ close tree(this);
				return temp1;
			}else{
				boolean temp2=false;
				if(r != null) {
				  //@ assert r != null;
				  temp2 = r.contains(x);
				} else {
					
				}
				//@ close tree(this);
				return temp2;
			}
		}
	}

	//@ requires tree(this);
	//@ ensures tree(this);
	public void add(int x)
	{
		//@ open tree(this);
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
		//@ close tree(this);
	}

	//@ requires tree(this);
	//@ ensures tree(this) &*& result == (this.right == null ? this.value : this.right.maximum());
	public int maximum()
	{
		//@ open tree(this);
		int v=this.value;
		Tree r=this.right;
		if(r==null){
			//@ close tree(this);
			return v;
		}else{
			int m= r.maximum();
			//@ close tree(this);
			return m;
		}
	}

	//@ requires tree(this);
	//@ ensures this == null ? true : tree(result);
	public Tree remove(int x)
	{
		//@ open tree(this);
		int v=this.value;
		Tree l=this.left;
		Tree r=this.right;
		if(x < v){
			if(l!=null){
				Tree temp=l.remove(x);
				this.left=temp;
				//@ close tree(this);
				return this;
			}
		}
		if(v < x){
			if(r!=null){
				Tree temp=r.remove(x);
				this.right=temp;
				//@ close tree(this);
				return this;
			}
		}
		if(v==x){
			if(l!=null&&r==null){
				//@ close tree(this);
				return l;
			}
			if(l==null&&r==null){
				//@ close tree(this);
				return null;
			}
			if(l==null&&r!=null){
				//@ close tree(this);
				return r;
			}
			if(l!=null&&r!=null){
				Tree temp=null;
				int m=l.maximum();
				this.value=m;
				temp=l.remove(m);
				this.left=temp;
				//@ close tree(this);
				return this;
			}
		}
		//@ close tree(this);
		return null; 
	}

	//@ requires true;
	//@ ensures true;
	public static void main(String[]  args)
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