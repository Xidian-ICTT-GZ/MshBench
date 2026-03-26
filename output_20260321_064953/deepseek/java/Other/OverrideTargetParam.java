class A 
{
    int i;
  
    /*@
    predicate valid() = this.i |-> _;
    @*/
    
    public A()
    //@ requires true;
    //@ ensures valid();
    {
        //@ close valid();
    }
      
    public int getI()
    //@ requires valid();
    //@ ensures valid() &*& result == this.i;
    {
        //@ open valid();
        return i;
        //@ close valid();
    }
}

class B extends A
{
    int j;
    
    /*@
    predicate valid() = this.valid@A() &*& this.j |-> _;
    @*/

    public B()
    //@ requires true;
    //@ ensures valid();
    {
        super();
        //@ close valid();
    }
    

    public int getI()
    //@ requires valid();
    //@ ensures valid() &*& result == this.i;
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