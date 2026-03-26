class A 
{
    int i;
  
    /*@
    predicate A_inv() = this.i |-> _;
    @*/
    
      
    public int getI()
    //@ requires A_inv();
    //@ ensures A_inv();
    
    
    {
        //@ open A_inv();
        int r = i;
        //@ close A_inv();
        return r;
    }
}

class B extends A
{
    int j;
    
    /*@
    predicate B_inv() = A_inv() &*& this.j |-> _;
    @*/
    
    

    public int getI()
    //@ requires B_inv();
    //@ ensures B_inv();
    
    
    {
        //@ open B_inv();
        int r = super.getI();
        //@ close B_inv();
        return r;
        
    }
}

class Program {
    public void test(B b) 
    //@ requires b != null &*& b.B_inv();
    //@ ensures b.B_inv();
      
      
    {
    	b.getI();
    }
}