package tree;

/*@
predicate Tree(Tree t;) =
    t != null
    &*& t.value |-> ?v
    &*& t.left |-> ?l
    &*& t.right |-> ?r
    &*& (l == null ? true : Tree(l))
    &*& (r == null ? true : Tree(r));
@*/

public class Tree{
	public int value;
	public Tree left;
	public Tree right;

	public Tree(int x)
	//@ requires true;
	//@ ensures Tree(this);
	{
	    	this.value=x;
		this.left=null;
		this.right=null;
		//@ close Tree(this);
	}
	public boolean contains(int x)
	//@ requires Tree(this);
	//@ ensures Tree(this);
	{
		//@ open Tree(this);
		int v=this.value;
		Tree l=this.left;
		Tree r=this.right;
		if(v==x){
			//@ close Tree(this);
			return true;
		}else{
			if(x < v){
				boolean temp1=false;
				if(l != null) {
				  //@ close Tree(l);
				  temp1 = l.contains(x);
				  //@ open Tree(l);
				} else {
				  
				  
				}
				//@ close Tree(this);
				return temp1;
			}else{
				boolean temp2=false;
				if(r != null) {
				  //@ close Tree(r);
				  temp2 = r.contains(x);
				  //@ open Tree(r);
				} else {
				  
				  
				}
				//@ close Tree(this);
				return temp2;
			}
		}
	}
	public void add(int x)
	//@ requires Tree(this);
	//@ ensures Tree(this);
	{
		//@ open Tree(this);
		int v=this.value;
		Tree l=this.left;
		
		
		Tree r=this.right;
		
		
		if(x < v){
			if(l!=null){
				//@ close Tree(l);
				l.add(x);
				//@ open Tree(l);
				
			}else{
				Tree temp=new Tree(x);
				this.left=temp;
				
			}
		}else{
			if(v < x){
				if(r!=null){
					//@ close Tree(r);
					r.add(x);
					//@ open Tree(r);
					
				}else{
					Tree temp=new Tree(x);
					this.right=temp;
					
				}
			}
		}
		//@ close Tree(this);
	}
	public int maximum()
	//@ requires Tree(this);
	//@ ensures Tree(this);
	{
		//@ open Tree(this);
		int v=this.value;
		Tree r=this.right;
		
		
		if(r==null){
			//@ close Tree(this);
			return v;
		}else{
			//@ close Tree(r);
			int m= r.maximum();
			//@ open Tree(r);
			//@ close Tree(this);
			return m;
		}
	}
	public Tree remove(int x)
	//@ requires Tree(this);
	//@ ensures result == null ? true : Tree(result);
	{
		//@ open Tree(this);
		int v=this.value;
		Tree l=this.left;
		
		
		Tree r=this.right;
		
		
		
		if(x < v){
			if(l!=null){
				//@ close Tree(l);
				Tree temp=l.remove(x);
				this.left=temp;
				//@ close Tree(this);
				return this;
			} else {
			    //@ close Tree(this);
			    return this;
			}
		}
		if(v < x){
			if(r!=null){
				//@ close Tree(r);
				Tree temp=r.remove(x);
				this.right=temp;
				//@ close Tree(this);
				return this;
			} else {
			    //@ close Tree(this);
			    return this;
			}
		}
		if(v==x){
			if(l!=null&&r==null){
				//@ close Tree(l);
				return l;
			}
			if(l==null&&r==null){
				
				return null;
			}
			if(l==null&&r!=null){
				//@ close Tree(r);
				return r;
			}
			if(l!=null&&r!=null){
				Tree temp=null;
				//@ close Tree(l);
				int m=l.maximum();
				this.value=m;
				
				temp=l.remove(m);
				this.left=temp;
				//@ close Tree(this);
				return this;
			}
		}
		//@ close Tree(this);
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
		//@ assert Tree(t1);
		b=t1.contains(2);
		//@ assert b == false;
		assert(!b);
		t1.add(2);

		a=t1.contains(2);
		assert(a);
		c=t1.contains(3);
		assert(c);
		t2=t1.remove(3);
		if(t2 != null) {
		  //@ assert Tree(t2);
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