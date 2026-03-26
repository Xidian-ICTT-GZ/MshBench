class A 
{
    int i;
    
    /*@
    predicate objectA() = this->i |-> _;
    @*/
      
    //@ requires objectA();
    //@ ensures objectA() &*& result == i;
    public int getI()
    {
        return i;
    }
}

class B extends A
{
    int j;
    
    /*@
    predicate objectB() = this->j |-> _ &*& objectA();
    @*/
    
    //@ requires objectB();
    //@ ensures objectB() &*& result == super.getI();
    public int getI()
    {
        return super.getI();
    }
}

class Program {
    //@ requires true;
    //@ ensures true;
    public void test(B b) 
    {
        b.getI();
    }
}