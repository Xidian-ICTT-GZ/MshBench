package tree;

/*@
predicate tree(Tree t) =
  t != null ?
    t.left |-> ?l &*& t.right |-> ?r &*& t.value |-> _ &*&
    (l != null ? tree(l) : true) &*& (r != null ? tree(r) : true)
  : true;
@*/

public class Tree{
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
	//@ ensures tree(this) &*& result == (exists y. tree(this) &*& this.value == y &*& y == x || 
	
	
	//@ pure
	public boolean contains(int x)
	
	
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
				  //@ open tree(this);
				  temp1 = l.contains(x);
				  //@ close tree(this);
				} else {
				  
				  
				}
				
				return temp1;
			}else{
				boolean temp2=false;
				if(r != null) {
				  //@ open tree(this);
				  temp2 = r.contains(x);
				  //@ close tree(this);
				} else {
				  
				  
				}
				
				return temp2;
			}
		}
	}
	//@ requires tree(this);
	//@ ensures tree(this);
	public void add(int x)
	
	
	{
		
		int v=this.value;
		Tree l=this.left;
		
		
		Tree r=this.right;
		
		
		if(x < v){
			if(l!=null){
				//@ open tree(this);
				l.add(x);
				//@ close tree(this);
				
				
			}else{
				Tree temp=new Tree(x);
				this.left=temp;
				
				
				
			}
		}else{
			if(v < x){
				if(r!=null){
					//@ open tree(this);
					r.add(x);
					//@ close tree(this);
					
					
				}else{
					Tree temp=new Tree(x);
					this.right=temp;
					
					
				}
			}
		}
	}
	//@ requires tree(this) &*& this != null;
	//@ ensures tree(this) &*& result >= this.value;
	//@ pure
	public int maximum()
	
	
	{
		
		int v=this.value;
		Tree r=this.right;
		
		
		if(r==null){
			
			return v;
		}else{
			//@ open tree(this);
			int m= r.maximum();
			//@ close tree(this);
			
			return m;
		}
	}
	//@ requires tree(this);
	//@ ensures tree(result);
	public Tree remove(int x)
	
	
	{
		
		int v=this.value;
		Tree l=this.left;
		
		
		Tree r=this.right;
		
		
		
		if(x < v){
			if(l!=null){
				//@ open tree(this);
				Tree temp=l.remove(x);
				this.left=temp;
				//@ close tree(this);
				
				return this;
			}
		}
		if(v < x){
			if(r!=null){
				//@ open tree(this);
				Tree temp=r.remove(x);
				this.right=temp;
				//@ close tree(this);
				
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
				//@ open tree(this);
				int m=l.maximum();
				this.value=m;
				
				temp=l.remove(m);
				this.left=temp;
				//@ close tree(this);
				
				return this;
			}
		}
		
		
		return null; 
	}
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