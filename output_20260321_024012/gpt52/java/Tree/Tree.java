package tree;

/*@
predicate TreeInv(Tree t) =
  t == null ?
    true
  :
    t.value |-> ?v &*& t.left |-> ?l &*& t.right |-> ?r &*& TreeInv(l) &*& TreeInv(r);
@*/

public class Tree{
	public int value;
	public Tree left;
	public Tree right;

	public Tree(int x)
	//@ requires true;
	//@ ensures TreeInv(this);
	{
	    	this.value=x;
		this.left=null;
		this.right=null;
		//@ close TreeInv(null);
		//@ close TreeInv(null);
		//@ close TreeInv(this);
	}
	public boolean contains(int x)
	//@ requires TreeInv(this);
	//@ ensures TreeInv(this);
	{
		//@ open TreeInv(this);
		int v=this.value;
		Tree l=this.left;
		Tree r=this.right;
		if(v==x){
			//@ close TreeInv(this);
			return true;
		}else{
			if(x < v){
				boolean temp1=false;
				if(l != null) {
				  temp1 = l.contains(x);
				} else {
				  
				  
				}
				//@ close TreeInv(this);
				return temp1;
			}else{
				boolean temp2=false;
				if(r != null) {
				  temp2 = r.contains(x);
				} else {
				  
				  
				}
				//@ close TreeInv(this);
				return temp2;
			}
		}
	}
	public void add(int x)
	//@ requires TreeInv(this);
	//@ ensures TreeInv(this);
	{
		//@ open TreeInv(this);
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
		//@ close TreeInv(this);
	}
	public int maximum()
	//@ requires TreeInv(this);
	//@ ensures TreeInv(this);
	{
		//@ open TreeInv(this);
		int v=this.value;
		Tree r=this.right;
		
		
		if(r==null){
			//@ close TreeInv(this);
			return v;
		}else{
			int m= r.maximum();
			//@ close TreeInv(this);
			return m;
		}
	}
	public Tree remove(int x)
	//@ requires TreeInv(this);
	//@ ensures TreeInv(result);
	{
		//@ open TreeInv(this);
		int v=this.value;
		Tree l=this.left;
		
		
		Tree r=this.right;
		
		
		
		if(x < v){
			if(l!=null){
				Tree temp=l.remove(x);
				this.left=temp;
				
				//@ close TreeInv(this);
				return this;
			}
		}
		if(v < x){
			if(r!=null){
				Tree temp=r.remove(x);
				this.right=temp;
				
				//@ close TreeInv(this);
				return this;
			}
		}
		if(v==x){
			if(l!=null&&r==null){
				//@ close TreeInv(r);
				//@ assert TreeInv(l);
				return l;
			}
			if(l==null&&r==null){
				//@ close TreeInv(l);
				//@ close TreeInv(r);
				return null;
			}
			if(l==null&&r!=null){
				//@ close TreeInv(l);
				//@ assert TreeInv(r);
				return r;
			}
			if(l!=null&&r!=null){
				Tree temp=null;
				int m=l.maximum();
				this.value=m;
				
				temp=l.remove(m);
				this.left=temp;
				
				//@ close TreeInv(this);
				return this;
			}
		}
		
		
		//@ close TreeInv(this);
		//@ close TreeInv(null);
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
		//@ assert TreeInv(t1);
		b=t1.contains(2);
		assert(!b);
		t1.add(2);

		a=t1.contains(2);
		assert(a);
		c=t1.contains(3);
		assert(c);
		t2=t1.remove(3);
		//@ assert TreeInv(t2);
		if(t2 != null) {
		  d= t2.contains(3);
		  assert(!d);

		  t2.add(3);
		  e= t2.contains(2);
		  assert(e);
		  t3=t2.remove(3);
		  //@ assert TreeInv(t3);
		  if(t3 != null) {
		    f=t3.contains(3);
		    assert(!f);
		  }
		}
	}
}