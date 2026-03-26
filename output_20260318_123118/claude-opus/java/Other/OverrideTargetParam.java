class A 
{
    int i;
    
    /*@ predicate inv_A(A a;) = a.i |-> ?v; @*/

      
    //@ requires inv_A(this);
    //@ ensures inv_A(this) &*& result == this.i;
    public int getI()
    {
        return i;
    }
}

class B extends A
{
    int j;
    
    /*@ predicate inv_B(B b;) =
          inv_A(b) &*& b.j |-> ?vj; @*/

    //@ requires inv_B(this);
    //@ ensures inv_B(this) &*& result == super.getI();
    public int getI()
    {
        return super.getI();
    }
}

class Program {
    //@ requires inv_B(b);
    //@ ensures inv_B(b);
    public void test(B b) 
    {
        b.getI();
    }
}