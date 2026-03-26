class A 
{
    int i;
    
    /*@
    predicate_family_instance object(A a) = a.i |-> ?val &*& true;
    @*/
    
    //@ requires this |-> ?a &*& object(this);
    //@ ensures this |-> ?a &*& object(this) &*& result == this.i;
    public int getI()
    {
        return i;
    }
}

class B extends A
{
    int j;
    
    /*@
    predicate_family_instance object(B b) = b.j |-> ?valj &*& b.i |-> ?vali &*& true;
    @*/
    
    //@ requires this |-> ?b &*& object(this);
    //@ ensures this |-> ?b &*& object(this) &*& result == this.i;
    public int getI()
    {
        return super.getI();
    }
}

class Program {
    //@ requires b |-> ?x &*& object(b);
    //@ ensures b |-> ?x &*& object(b);
    public void test(B b) 
    {
    	b.getI();
    }
}