package tree;

public class Tree{
	public int value;
	public Tree left;
	public Tree right;

	/*@
	predicate tree() =
		this.value |-> ?v &*& this.left |-> ?l &*& this.right |-> ?r
		&*& (l == null ? true : l.tree())
		&*& (r == null ? true : r.tree());
	@*/

	//@ requires true;
	//@ ensures this.tree();
	public Tree(int x)
	
	
	{
	    	this.value=x;
		this.left=null;
		this.right=null;
		
		
		
		
		//@ close this.tree();
	}

	//@ requires this.tree();
	//@ ensures this.tree();
	public boolean contains(int x)
	
	
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
				  //@ open l.tree();
				  //@ close l.tree();
				  temp1 = l.contains(x);
				} else {
				  
				  
				}
				//@ close this.tree();
				return temp1;
			}else{
				boolean temp2=false;
				if(r != null) {
				  //@ open r.tree();
				  //@ close r.tree();
				  temp2 = r.contains(x);
				} else {
				  
				  
				}
				//@ close this.tree();
				return temp2;
			}
		}
	}

	//@ requires this.tree();
	//@ ensures this.tree();
	public void add(int x)
	
	
	{
		//@ open this.tree();
		int v=this.value;
		Tree l=this.left;
		
		
		Tree r=this.right;
		
		
		if(x < v){
			if(l!=null){
				//@ open l.tree();
				//@ close l.tree();
				l.add(x);
				
				
			}else{
				Tree temp=new Tree(x);
				//@ open temp.tree();
				//@ close temp.tree();
				this.left=temp;
				
				
				
			}
		}else{
			if(v < x){
				if(r!=null){
					//@ open r.tree();
					//@ close r.tree();
					r.add(x);
					
					
				}else{
					Tree temp=new Tree(x);
					//@ open temp.tree();
					//@ close temp.tree();
					this.right=temp;
					
					
				}
			}
		}
		//@ close this.tree();
	}

	//@ requires this.tree();
	//@ ensures this.tree() &*& result >= 0 ? true : true;
	public int maximum()
	
	
	{
		//@ open this.tree();
		int v=this.value;
		Tree r=this.right;
		
		
		if(r==null){
			//@ close this.tree();
			return v;
		}else{
			//@ open r.tree();
			//@ close r.tree();
			int m= r.maximum();
			//@ close this.tree();
			return m;
		}
	}

	//@ requires this.tree();
	//@ ensures (result == null ? true : result.tree());
	public Tree remove(int x)
	
	
	{
		//@ open this.tree();
		int v=this.value;
		Tree l=this.left;
		
		
		Tree r=this.right;
		
		
		
		if(x < v){
			if(l!=null){
				//@ open l.tree();
				//@ close l.tree();
				Tree temp=l.remove(x);
				this.left=temp;
				//@ close this.tree();
				return this;
			}
		}
		if(v < x){
			if(r!=null){
				//@ open r.tree();
				//@ close r.tree();
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
				//@ open l.tree();
				//@ close l.tree();
				int m=l.maximum();
				this.value=m;
				
				//@ open l.tree();
				//@ close l.tree();
				temp=l.remove(m);
				this.left=temp;
				
				//@ close this.tree();
				return this;
			}
		}
		
		
		//@ close this.tree();
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
		//@ open t1.tree();
		//@ close t1.tree();
		b=t1.contains(2);
		assert(!b);
		//@ open t1.tree();
		//@ close t1.tree();
		t1.add(2);

		//@ open t1.tree();
		//@ close t1.tree();
		a=t1.contains(2);
		assert(a);
		//@ open t1.tree();
		//@ close t1.tree();
		c=t1.contains(3);
		assert(c);
		//@ open t1.tree();
		//@ close t1.tree();
		t2=t1.remove(3);
		if(t2 != null) {
		  //@ open t2.tree();
		  //@ close t2.tree();
		  d= t2.contains(3);
		  assert(!d);

		  //@ open t2.tree();
		  //@ close t2.tree();
		  t2.add(3);
		  //@ open t2.tree();
		  //@ close t2.tree();
		  e= t2.contains(2);
		  assert(e);
		  //@ open t2.tree();
		  //@ close t2.tree();
		  t3=t2.remove(3);
		  if(t3 != null) {
		    //@ open t3.tree();
		    //@ close t3.tree();
		    f=t3.contains(3);
		    assert(!f);
		  }
		}
	}
}