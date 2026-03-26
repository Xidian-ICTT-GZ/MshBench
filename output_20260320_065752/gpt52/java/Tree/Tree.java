package tree;

/*@
predicate TreeNode(Tree t) =
  t.value |-> ?v &*& t.left |-> ?l &*& t.right |-> ?r &*&
  (l == null ? true : TreeNode(l)) &*& (r == null ? true : TreeNode(r));
@*/

public class Tree{
	public int value;
	public Tree left;
	public Tree right;

	//@ requires true;
	//@ ensures TreeNode(this);
	public Tree(int x)
	
	
	{
	    	this.value=x;
		this.left=null;
		this.right=null;
		//@ close TreeNode(this);
		
		
		
		
		
	}
	//@ requires TreeNode(this);
	//@ ensures TreeNode(this);
	public boolean contains(int x)
	
	
	{
		//@ open TreeNode(this);
		int v=this.value;
		Tree l=this.left;
		Tree r=this.right;
		if(v==x){
			//@ close TreeNode(this);
			return true;
		}else{
			if(x < v){
				boolean temp1=false;
				if(l != null) {
				  temp1 = l.contains(x);
				} else {
				  
				  
				}
				//@ close TreeNode(this);
				return temp1;
			}else{
				boolean temp2=false;
				if(r != null) {
				  temp2 = r.contains(x);
				} else {
				  
				  
				}
				//@ close TreeNode(this);
				return temp2;
			}
		}
	}
	//@ requires TreeNode(this);
	//@ ensures TreeNode(this);
	public void add(int x)
	
	
	{
		//@ open TreeNode(this);
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
		//@ close TreeNode(this);
	}
	//@ requires TreeNode(this);
	//@ ensures TreeNode(this);
	public int maximum()
	
	
	{
		//@ open TreeNode(this);
		int v=this.value;
		Tree r=this.right;
		
		
		if(r==null){
			//@ close TreeNode(this);
			return v;
		}else{
			int m= r.maximum();
			//@ close TreeNode(this);
			return m;
		}
	}
	//@ requires TreeNode(this);
	//@ ensures result == null ? true : TreeNode(result);
	public Tree remove(int x)
	
	
	{
		//@ open TreeNode(this);
		int v=this.value;
		Tree l=this.left;
		
		
		Tree r=this.right;
		
		
		
		if(x < v){
			if(l!=null){
				Tree temp=l.remove(x);
				this.left=temp;
				//@ close TreeNode(this);
				return this;
			}
		}
		if(v < x){
			if(r!=null){
				Tree temp=r.remove(x);
				this.right=temp;
				//@ close TreeNode(this);
				return this;
			}
		}
		if(v==x){
			if(l!=null&&r==null){
				//@ close TreeNode(r);
				return l;
			}
			if(l==null&&r==null){
				//@ close TreeNode(this);
				return null;
			}
			if(l==null&&r!=null){
				//@ close TreeNode(l);
				return r;
			}
			if(l!=null&&r!=null){
				Tree temp=null;
				int m=l.maximum();
				this.value=m;
				
				temp=l.remove(m);
				this.left=temp;
				//@ close TreeNode(this);
				return this;
			}
		}
		
		
		//@ close TreeNode(this);
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