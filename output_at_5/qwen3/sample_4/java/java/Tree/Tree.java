package tree;

public class Tree{
	public int value;
	public Tree left;
	public Tree right;

	//@ requires true;
	//@ ensures true;
	public Tree(int x)
	
	
	{
	    	this.value=x;
		this.left=null;
		this.right=null;
		
		
		
		
		
	}
	
	//@ requires true;
	//@ ensures true;
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
				  temp1 = l.contains(x);
				} else {
				  
				  
				}
				
				return temp1;
			}else{
				boolean temp2=false;
				if(r != null) {
				  temp2 = r.contains(x);
				} else {
				  
				  
				}
				
				return temp2;
			}
		}
	}
	
	//@ requires true;
	//@ ensures true;
	public void add(int x)
	
	
	{
		
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
	}
	
	//@ requires true;
	//@ ensures true;
	public int maximum()
	
	
	{
		
		int v=this.value;
		Tree r=this.right;
		
		
		if(r==null){
			
			return v;
		}else{
			int m= r.maximum();
			
			return m;
		}
	}
	
	//@ requires true;
	//@ ensures true;
	public Tree remove(int x)
	
	
	{
		
		int v=this.value;
		Tree l=this.left;
		
		
		Tree r=this.right;
		
		
		
		if(x < v){
			if(l!=null){
				Tree temp=l.remove(x);
				this.left=temp;
				
				return this;
			}
		}
		if(v < x){
			if(r!=null){
				Tree temp=r.remove(x);
				this.right=temp;
				
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
				int m=l.maximum();
				this.value=m;
				
				temp=l.remove(m);
				this.left=temp;
				
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