package tree;

public class Tree{
	public int value;
	public Tree left;
	public Tree right;

	/*@
	predicate tree() =
		this.value |-> ?v &*& this.left |-> ?l &*& this.right |-> ?r &*&
		(l == null ? true : l.tree()) &*& (r == null ? true : r.tree());
	@*/

	public Tree(int x)
	
	
	//@ requires true;
	//@ ensures this.tree();
	{
	    	this.value=x;
		this.left=null;
		this.right=null;
		
		
		
		
		
	}
	public boolean contains(int x)
	
	
	//@ requires this.tree();
	//@ ensures this.tree();
	{
		//@ open this.tree();
		int v=this.value;
		Tree l=this.left;
		Tree r=this.right;
		if(v==x){
			//@ close this.tree();
			return true;
		}else{
			if(x < v){
				boolean temp1=false;
				if(l != null) {
				  temp1 = l.contains(x);
				} else {
				  
				  
				}
				//@ close this.tree();
				return temp1;
			}else{
				boolean temp2=false;
				if(r != null) {
				  temp2 = r.contains(x);
				} else {
				  
				  
				}
				//@ close this.tree();
				return temp2;
			}
		}
	}
	public void add(int x)
	
	
	//@ requires this.tree();
	//@ ensures this.tree();
	{
		//@ open this.tree();
		int v=this.value;
		Tree l=this.left;
		
		
		Tree r=this.right;
		
		
		if(x < v){
			if(l!=null){
				l.add(x);
				//@ close this.tree();
				
				
			}else{
				Tree temp=new Tree(x);
				//@ open temp.tree();
				this.left=temp;
				//@ close temp.tree();
				//@ close this.tree();
				
				
				
			}
		}else{
			if(v < x){
				if(r!=null){
					r.add(x);
					//@ close this.tree();
					
					
				}else{
					Tree temp=new Tree(x);
					//@ open temp.tree();
					this.right=temp;
					//@ close temp.tree();
					//@ close this.tree();
					
					
				}
			} else {
				//@ close this.tree();
			}
		}
	}
	public int maximum()
	
	
	//@ requires this.tree();
	//@ ensures this.tree();
	{
		//@ open this.tree();
		int v=this.value;
		Tree r=this.right;
		
		
		if(r==null){
			//@ close this.tree();
			return v;
		}else{
			int m= r.maximum();
			//@ close this.tree();
			return m;
		}
	}
	public Tree remove(int x)
	
	
	//@ requires this.tree();
	//@ ensures (result == null ? true : result.tree());
	{
		//@ open this.tree();
		int v=this.value;
		Tree l=this.left;
		
		
		Tree r=this.right;
		
		
		
		if(x < v){
			if(l!=null){
				Tree temp=l.remove(x);
				this.left=temp;
				//@ close this.tree();
				return this;
			}
		}
		if(v < x){
			if(r!=null){
				Tree temp=r.remove(x);
				this.right=temp;
				//@ close this.tree();
				return this;
			}
		}
		if(v==x){
			if(l!=null&&r==null){
				//@ close this.tree();
				return l;
			}
			if(l==null&&r==null){
				//@ close this.tree();
				return null;
			}
			if(l==null&&r!=null){
				//@ close this.tree();
				return r;
			}
			if(l!=null&&r!=null){
				Tree temp=null;
				int m=l.maximum();
				this.value=m;
				
				temp=l.remove(m);
				this.left=temp;
				//@ close this.tree();
				return this;
			}
		}
		
		
		//@ close this.tree();
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