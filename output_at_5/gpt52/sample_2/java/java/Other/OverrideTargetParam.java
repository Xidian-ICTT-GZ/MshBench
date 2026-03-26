class A 
{
    int i;
  
    /*@
    predicate A_inv() = this.i |-> _;
    @*/
    
      
    public int getI()
    //@ requires this.A_inv();
    //@ ensures this.A_inv();
    
    
    {
        //@ open A_inv();
        int res = i;
        //@ close A_inv();
        return res;
    }
}

class B extends A
{
    int j;
    
    /*@
    predicate B_inv() = A_inv() &*& this.j |-> _;
    @*/
    
    

    public int getI()
    //@ requires this.B_inv();
    //@ ensures this.B_inv();
    
    
    {
        
        //@ open B_inv();
        int res = super.getI();
        //@ close B_inv();
        return res;
        
    }
}

class Program {
    public void test(B b) 
    //@ requires b.B_inv();
    //@ ensures b.B_inv();
      
      
    {
    	b.getI();
    }
}