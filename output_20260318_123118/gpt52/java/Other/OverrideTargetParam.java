class A 
{
    int i;
    
    /*@ predicate A_inv() = this.i |-> ?v; @*/
      
    public int getI()
    //@ requires A_inv();
    //@ ensures A_inv() &*& result == i;
    {
        return i;
    }
}

class B extends A
{
    int j;
    
    /*@ predicate B_inv() = A_inv() &*& this.j |-> ?w; @*/

    public int getI()
    //@ requires B_inv();
    //@ ensures B_inv() &*& result == i;
    {
        
        return super.getI();
        
    }
}

class Program {
    public void test(B b) 
    //@ requires b != null &*& b.B_inv();
    //@ ensures b.B_inv();
    {
    	b.getI();
    }
}