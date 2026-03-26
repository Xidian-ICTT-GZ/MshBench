package tree;

/*@
predicate Tree(Tree t; int v, Tree l, Tree r) =
    t != null
    &*& t.value |-> v
    &*& t.left |-> l
    &*& t.right |-> r
    &*& (l == null ? true : Tree(l, _, _, _))
    &*& (r == null ? true : Tree(r, _, _, _));
@*/

public class Tree{
	public int value;
	public Tree left;
	public Tree right;

	public Tree(int x)
	//@ requires true;
	//@ ensures Tree(this, x, null, null);
	{
	    	this.value=x;
		this.left=null;
		this.right=null;
	}
	
	public boolean contains(int x)
	//@ requires Tree(this, ?v, ?l, ?r);
	//@ ensures Tree(this, v, l, r) &*& result == true || Tree(this, v, l, r) &*& result == false;
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
				  //@ open Tree(this, v, l, r);
				  temp1 = l.contains(x);
				  //@ close Tree(this, v, l, r);
				} else {
				}
				return temp1;
			}else{
				boolean temp2=false;
				if(r != null) {
				  //@ open Tree(this, v, l, r);
				  temp2 = r.contains(x);
				  //@ close Tree(this, v, l, r);
				} else {
				}
				return temp2;
			}
		}
	}
	
	public void add(int x)
	//@ requires Tree(this, ?v, ?l, ?r);
	//@ ensures Tree(this, v, l, r);
	{
		int v=this.value;
		Tree l=this.left;
		Tree r=this.right;
		if(x < v){
			if(l!=null){
				//@ open Tree(this, v, l, r);
				l.add(x);
				//@ close Tree(this, v, l, r);
			}else{
				Tree temp=new Tree(x);
				this.left=temp;
				//@ close Tree(temp, x, null, null);
				//@ close Tree(this, v, temp, r);
			}
		}else{
			if(v < x){
				if(r!=null){
					//@ open Tree(this, v, l, r);
					r.add(x);
					//@ close Tree(this, v, l, r);
				}else{
					Tree temp=new Tree(x);
					this.right=temp;
					//@ close Tree(temp, x, null, null);
					//@ close Tree(this, v, l, temp);
				}
			}
		}
	}
	
	public int maximum()
	//@ requires Tree(this, ?v, ?l, ?r);
	//@ ensures Tree(this, v, l, r);
	{
		int v=this.value;
		Tree r=this.right;
		if(r==null){
			return v;
		}else{
			//@ open Tree(this, v, l, r);
			int m= r.maximum();
			//@ close Tree(this, v, l, r);
			return m;
		}
	}
	
	public Tree remove(int x)
	//@ requires Tree(this, ?v, ?l, ?r);
	//@ ensures result == null ? true : Tree(result, _, _, _);
	{
		int v=this.value;
		Tree l=this.left;
		Tree r=this.right;
		if(x < v){
			if(l!=null){
				//@ open Tree(this, v, l, r);
				Tree temp=l.remove(x);
				this.left=temp;
				//@ close Tree(this, v, temp, r);
				return this;
			}
		}
		if(v < x){
			if(r!=null){
				//@ open Tree(this, v, l, r);
				Tree temp=r.remove(x);
				this.right=temp;
				//@ close Tree(this, v, l, temp);
				return this;
			}
		}
		if(v==x){
			if(l!=null&&r==null){
				//@ open Tree(this, v, l, r);
				return l;
			}
			if(l==null&&r==null){
				return null;
			}
			if(l==null&&r!=null){
				//@ open Tree(this, v, l, r);
				return r;
			}
			if(l!=null&&r!=null){
				Tree temp=null;
				//@ open Tree(this, v, l, r);
				int m=l.maximum();
				this.value=m;
				temp=l.remove(m);
				this.left=temp;
				//@ close Tree(this, m, temp, r);
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
		//@ close Tree(t1, 3, null, null);
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