class A 
{
    int i;
    
    /*@
    predicate objectInv() = this->i |-> _;
    @*/
      
    public int getI()
    //@ requires objectInv();
    //@ ensures objectInv() &*& result == i;
    {
        return i;
    }
}

class B extends A
{
    int j;
    
    /*@
    predicate objectInv() = this->j |-> _ &*& super.objectInv();
    @*/
    
    public int getI()
    //@ requires objectInv();
    //@ ensures objectInv() &*& result == super.i;
    {
        return super.getI();
    }
}

class Program {
    public void test(B b) 
    //@ requires b.objectInv();
    //@ ensures b.objectInv();
    {
    	b.getI();
    }
}