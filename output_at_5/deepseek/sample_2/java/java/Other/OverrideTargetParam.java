class A 
{
    int i;
  
    /*@
    predicate valid() = this.i |-> _;
    @*/
    
      
    public int getI()
    //@ requires valid();
    //@ ensures valid();
    //@ ensures result == this.i;
    
    {
        return i;
    }
}

class B extends A
{
    int j;
    
    /*@
    predicate valid() = super.valid() &*& this.j |-> _;
    @*/

    public int getI()
    //@ requires valid();
    //@ ensures valid();
    //@ ensures result == this.i;
    
    {
        //@ open valid();
        int r = super.getI();
        //@ close valid();
        return r;
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