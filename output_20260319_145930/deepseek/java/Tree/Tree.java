package tree;

/*@
predicate Tree(Tree t; int value, Tree left, Tree right) =
    t != null &*&
    t.value |-> value &*&
    t.left |-> left &*&
    t.right |-> right &*&
    (left == null ? true : Tree(left, _, _, _)) &*&
    (right == null ? true : Tree(right, _, _, _));
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
		//@ close Tree(this, x, null, null);
	}
	
	public boolean contains(int x)
	//@ requires Tree(this, ?v, ?l, ?r);
	//@ ensures Tree(this, v, l, r) &*& result == (x == v || (x < v && l != null && l.contains(x)) || (v < x && r != null && r.contains(x)));
	{
		//@ open Tree(this, v, l, r);
		int v=this.value;
		Tree l=this.left;
		Tree r=this.right;
		if(v==x){
			//@ close Tree(this, v, l, r);
			return true;
		}else{
			if(x < v){
				boolean temp1=false;
				if(l != null) {
				  //@ assert l != null;
				  //@ open Tree(this, v, l, r);
				  //@ close Tree(l, _, _, _);
				  temp1 = l.contains(x);
				  //@ open Tree(l, _, _, _);
				  //@ close Tree(this, v, l, r);
				} else {
				  
				  
				}
				//@ close Tree(this, v, l, r);
				return temp1;
			}else{
				boolean temp2=false;
				if(r != null) {
				  //@ assert r != null;
				  //@ open Tree(this, v, l, r);
				  //@ close Tree(r, _, _, _);
				  temp2 = r.contains(x);
				  //@ open Tree(r, _, _, _);
				  //@ close Tree(this, v, l, r);
				} else {
				  
				  
				}
				//@ close Tree(this, v, l, r);
				return temp2;
			}
		}
	}
	
	public void add(int x)
	//@ requires Tree(this, ?v, ?l, ?r);
	//@ ensures Tree(this, v, l, r);
	{
		//@ open Tree(this, v, l, r);
		int v=this.value;
		Tree l=this.left;
		Tree r=this.right;
		if(x < v){
			if(l!=null){
				//@ close Tree(l, _, _, _);
				l.add(x);
				//@ open Tree(l, _, _, _);
			}else{
				Tree temp=new Tree(x);
				this.left=temp;
			}
		}else{
			if(v < x){
				if(r!=null){
					//@ close Tree(r, _, _, _);
					r.add(x);
					//@ open Tree(r, _, _, _);
				}else{
					Tree temp=new Tree(x);
					this.right=temp;
				}
			}
		}
		//@ close Tree(this, v, l, r);
	}
	
	public int maximum()
	//@ requires Tree(this, ?v, ?l, ?r);
	//@ ensures Tree(this, v, l, r);
	{
		//@ open Tree(this, v, l, r);
		int v=this.value;
		Tree r=this.right;
		if(r==null){
			//@ close Tree(this, v, l, r);
			return v;
		}else{
			//@ close Tree(r, _, _, _);
			int m= r.maximum();
			//@ open Tree(r, _, _, _);
			//@ close Tree(this, v, l, r);
			return m;
		}
	}
	
	public Tree remove(int x)
	//@ requires Tree(this, ?v, ?l, ?r);
	//@ ensures result == null ? true : Tree(result, _, _, _);
	{
		//@ open Tree(this, v, l, r);
		int v=this.value;
		Tree l=this.left;
		Tree r=this.right;
		if(x < v){
			if(l!=null){
				//@ close Tree(l, _, _, _);
				Tree temp=l.remove(x);
				this.left=temp;
				//@ close Tree(this, v, l, r);
				return this;
			}
		}
		if(v < x){
			if(r!=null){
				//@ close Tree(r, _, _, _);
				Tree temp=r.remove(x);
				this.right=temp;
				//@ close Tree(this, v, l, r);
				return this;
			}
		}
		if(v==x){
			if(l!=null&&r==null){
				//@ close Tree(l, _, _, _);
				return l;
			}
			if(l==null&&r==null){
				return null;
			}
			if(l==null&&r!=null){
				//@ close Tree(r, _, _, _);
				return r;
			}
			if(l!=null&&r!=null){
				Tree temp=null;
				//@ close Tree(l, _, _, _);
				int m=l.maximum();
				this.value=m;
				temp=l.remove(m);
				this.left=temp;
				//@ close Tree(this, v, l, r);
				return this;
			}
		}
		//@ close Tree(this, v, l, r);
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
		//@ open Tree(t1, _, _, _);
		//@ close Tree(t1, _, _, _);
		b=t1.contains(2);
		assert(!b);
		//@ open Tree(t1, _, _, _);
		//@ close Tree(t1, _, _, _);
		t1.add(2);

		//@ open Tree(t1, _, _, _);
		//@ close Tree(t1, _, _, _);
		a=t1.contains(2);
		assert(a);
		//@ open Tree(t1, _, _, _);
		//@ close Tree(t1, _, _, _);
		c=t1.contains(3);
		assert(c);
		//@ open Tree(t1, _, _, _);
		//@ close Tree(t1, _, _, _);
		t2=t1.remove(3);
		if(t2 != null) {
		  //@ open Tree(t2, _, _, _);
		  //@ close Tree(t2, _, _, _);
		  d= t2.contains(3);
		  assert(!d);

		  //@ open Tree(t2, _, _, _);
		  //@ close Tree(t2, _, _, _);
		  t2.add(3);
		  //@ open Tree(t2, _, _, _);
		  //@ close Tree(t2, _, _, _);
		  e= t2.contains(2);
		  assert(e);
		  //@ open Tree(t2, _, _, _);
		  //@ close Tree(t2, _, _, _);
		  t3=t2.remove(3);
		  if(t3 != null) {
		    //@ open Tree(t3, _, _, _);
		    //@ close Tree(t3, _, _, _);
		    f=t3.contains(3);
		    assert(!f);
		  }
		}
	}
}