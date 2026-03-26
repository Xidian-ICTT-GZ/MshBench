class A 
{
    int i;
    
    /*@
    predicate thisInv() = this->i |-> _;
    @*/
      
    public int getI()
    //@ requires thisInv();
    //@ ensures thisInv() &*& result == i;
    {
        return i;
    }
}

class B extends A
{
    int j;
    
    /*@
    predicate thisInv() = this->j |-> _ &*& super.thisInv();
    @*/

    public int getI()
    //@ requires thisInv();
    //@ ensures thisInv() &*& result == super.i;
    {
        return super.getI();
    }
}

class Program {
    public void test(B b) 
    //@ requires b.thisInv();
    //@ ensures b.thisInv();
    {
    	b.getI();
    }
}