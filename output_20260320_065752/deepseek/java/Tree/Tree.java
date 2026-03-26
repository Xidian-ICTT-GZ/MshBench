package tree;

/*@
predicate Tree(Tree t; int value, Tree left, Tree right) =
    t != null
    &*& t.value |-> value
    &*& t.left |-> left
    &*& t.right |-> right
    &*& (left == null ? true : Tree(left, _, _, _))
    &*& (right == null ? true : Tree(right, _, _, _));
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
				  temp1 = l.contains(x);
				} else {
				  
				  
				}
				//@ close Tree(this, v, l, r);
				return temp1;
			}else{
				boolean temp2=false;
				if(r != null) {
				  //@ assert r != null;
				  temp2 = r.contains(x);
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
			int m= r.maximum();
			//@ close Tree(this, v, l, r);
			return m;
		}
	}
	public Tree remove(int x)
	//@ requires Tree(this, ?v, ?l, ?r);
	//@ ensures Tree(result, _, _, _) &*& result == null ? true : true;
	{
		//@ open Tree(this, v, l, r);
		int v=this.value;
		Tree l=this.left;
		
		
		Tree r=this.right;
		
		
		
		if(x < v){
			if(l!=null){
				Tree temp=l.remove(x);
				this.left=temp;
				//@ close Tree(this, v, l, r);
				return this;
			}
		}
		if(v < x){
			if(r!=null){
				Tree temp=r.remove(x);
				this.right=temp;
				//@ close Tree(this, v, l, r);
				return this;
			}
		}
		if(v==x){
			if(l!=null&&r==null){
				//@ close Tree(this, v, l, r);
				return l;
			}
			if(l==null&&r==null){
				
				
				//@ close Tree(this, v, l, r);
				return null;
			}
			if(l==null&&r!=null){
				//@ close Tree(this, v, l, r);
				return r;
			}
			if(l!=null&&r!=null){
				Tree temp=null;
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
		//@ assert Tree(t1, 3, null, null);
		b=t1.contains(2);
		assert(!b);
		t1.add(2);

		a=t1.contains(2);
		assert(a);
		c=t1.contains(3);
		assert(c);
		t2=t1.remove(3);
		if(t2 != null) {
		  //@ assert Tree(t2, _, _, _);
		  d= t2.contains(3);
		  assert(!d);

		  t2.add(3);
		  e= t2.contains(2);
		  assert(e);
		  t3=t2.remove(3);
		  if(t3 != null) {
		    //@ assert Tree(t3, _, _, _);
		    f=t3.contains(3);
		    assert(!f);
		  }
		}
	}
}