package tree;

/*@ 
predicate Tree(Tree t; int min, int max) =
  t != null ?
    min <= t.value &*& t.value <= max &*&
    Tree(t.left, min, t.value) &*&
    Tree(t.right, t.value, max)
  :
    true;
@*/

public class Tree{
	public int value;
	public Tree left;
	public Tree right;

	//@ requires true;
	//@ ensures Tree(this, Integer.MIN_VALUE, Integer.MAX_VALUE);
	public Tree(int x)
	
	
	{
	    	this.value=x;
		this.left=null;
		this.right=null;
		
		
		
		
		
	}
	
	//@ requires Tree(this, ?min, ?max);
	//@ ensures Tree(this, min, max) &*& result == (exists i. min <= i &*& i <= max &*& i == x);
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
				  //@ open Tree(this, min, max);
				  temp1 = l.contains(x);
				  //@ close Tree(this, min, max);
				} else {
				  
				  
				}
				
				return temp1;
			}else{
				boolean temp2=false;
				if(r != null) {
				  //@ open Tree(this, min, max);
				  temp2 = r.contains(x);
				  //@ close Tree(this, min, max);
				} else {
				  
				  
				}
				
				return temp2;
			}
		}
	}
	
	//@ requires Tree(this, ?min, ?max);
	//@ ensures Tree(this, min, max);
	public void add(int x)
	
	
	{
		
		int v=this.value;
		Tree l=this.left;
		
		
		Tree r=this.right;
		
		
		if(x < v){
			if(l!=null){
				//@ open Tree(this, min, max);
				l.add(x);
				//@ close Tree(this, min, max);
				
				
			}else{
				Tree temp=new Tree(x);
				//@ open Tree(this, min, max);
				this.left=temp;
				//@ close Tree(this, min, max);
				
				
				
			}
		}else{
			if(v < x){
				if(r!=null){
					//@ open Tree(this, min, max);
					r.add(x);
					//@ close Tree(this, min, max);
					
					
				}else{
					Tree temp=new Tree(x);
					//@ open Tree(this, min, max);
					this.right=temp;
					//@ close Tree(this, min, max);
					
					
				}
			}
		}
	}
	
	//@ requires Tree(this, ?min, ?max) &*& this.right == null;
	//@ ensures Tree(this, min, max) &*& result == this.value;
	public int maximum()
	
	
	{
		
		int v=this.value;
		Tree r=this.right;
		
		
		if(r==null){
			
			return v;
		}else{
			//@ open Tree(this, min, max);
			int m= r.maximum();
			//@ close Tree(this, min, max);
			
			return m;
		}
	}
	
	//@ requires Tree(this, ?min, ?max);
	//@ ensures Tree(result, min, max) &*& (result != null ? Tree(result, min, max) : true);
	public Tree remove(int x)
	
	
	{
		
		int v=this.value;
		Tree l=this.left;
		
		
		Tree r=this.right;
		
		
		
		if(x < v){
			if(l!=null){
				//@ open Tree(this, min, max);
				Tree temp=l.remove(x);
				this.left=temp;
				//@ close Tree(this, min, max);
				
				return this;
			}
		}
		if(v < x){
			if(r!=null){
				//@ open Tree(this, min, max);
				Tree temp=r.remove(x);
				this.right=temp;
				//@ close Tree(this, min, max);
				
				return this;
			}
		}
		if(v==x){
			if(l!=null&&r==null){
				//@ open Tree(this, min, max);
				return l;
			}
			if(l==null&&r==null){
				//@ open Tree(this, min, max);
				return null;
			}
			if(l==null&&r!=null){
				//@ open Tree(this, min, max);
				return r;
			}
			if(l!=null&&r!=null){
				Tree temp=null;
				//@ open Tree(this, min, max);
				int m=l.maximum();
				this.value=m;
				
				temp=l.remove(m);
				this.left=temp;
				//@ close Tree(this, min, max);
				
				return this;
			}
		}
		
		
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