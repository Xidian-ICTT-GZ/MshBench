class A 
{
    int i;
    
    /*@ predicate Ainv(A this) = this.i |-> ?v; @*/
    
    //@ requires Ainv(this);
    //@ ensures Ainv(this) &*& result == this.i;
    public int getI()
    {
        return i;
    }
}

class B extends A
{
    int j;
    
    /*@ predicate Binv(B this) = Ainv(this) &*& this.j |-> ?w; @*/
    
    //@ requires Binv(this);
    //@ ensures Binv(this) &*& result == this.i;
    public int getI()
    {
        return super.getI();
    }
}

class Program {
    //@ requires Binv(b);
    //@ ensures Binv(b);
    public void test(B b) 
    {
    	b.getI();
    }
}