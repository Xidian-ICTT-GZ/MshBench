class A 
{
    int i;
    
    /*@
    predicate object(self;) = this == self &*& this.i |-> ?value;
    @*/

    //@ requires object(this);
    //@ ensures object(this) &*& result == i;
    public int getI()
    {
        return i;
    }
}

class B extends A
{
    int j;
    
    /*@
    predicate object(self;) = this == self &*& this.i |-> ?ivalue &*& this.j |-> ?jvalue;
    @*/

    //@ requires object(this);
    //@ ensures object(this) &*& result == i;
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