class A 
{
    int i;
  
    //@ predicate valid() = this.i |-> _;
    
    //@ requires valid();
    //@ ensures valid() &*& result == this.i;
    public int getI()
    {
        //@ open valid();
        return i;
        //@ close valid();
    }
}

class B extends A
{
    int j;
    
    //@ predicate valid() = this.valid@A() &*& this.j |-> _;
    
    //@ requires valid();
    //@ ensures valid();
    public int getI()
    {
        //@ open valid();
        int result = super.getI();
        //@ close valid();
        return result;
    }
}

class Program {
    //@ requires b.valid();
    //@ ensures b.valid();
    public void test(B b) 
    {
        //@ open b.valid();
        //@ close b.valid@A();
        b.getI();
        //@ open b.valid@A();
        //@ close b.valid();
    }
}