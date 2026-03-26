class A 
{
    int i;
  
    //@ predicate valid() = this.i |-> _;
      
    public int getI()
    //@ requires valid();
    //@ ensures valid() &*& result == this.i;
    
    {
        return i;
    }
}

class B extends A
{
    int j;
    
    //@ predicate valid() = A.valid()() &*& this.j |-> _;

    public int getI()
    //@ requires valid();
    //@ ensures valid() &*& result == this.i;
    
    {
        //@ open valid();
        //@ close A.valid()();
        return super.getI();
        //@ close valid();
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