class A 
{
    int i;
  
    //@ predicate valid() = this.i |-> ?v;
    
      
    public int getI()
    //@ requires valid();
    //@ ensures valid() &*& result == i;
    
    {
        return i;
    }
}

class B extends A
{
    int j;
    
    //@ predicate valid() = A.valid()() &*& this.j |-> ?v;

    public int getI()
    //@ requires valid();
    //@ ensures valid() &*& result == i;
    
    {
        
        return super.getI();
        
    }
}

class Program {
    public void test(B b) 
    //@ requires b.valid();
    //@ ensures b.valid();
      
      
    {
    	b.getI();
    }
}