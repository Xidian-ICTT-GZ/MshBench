class A 
{
    int i;
  
    /*@
    predicate A_inv() = this.i |-> ?v;
    @*/
      
    public int getI()
    //@ requires this.A_inv();
    //@ ensures this.A_inv() &*& result == i;
    {
        return i;
    }
}

class B extends A
{
    int j;
    
    /*@
    predicate B_inv() = this.A_inv() &*& this.j |-> ?w;
    @*/

    public int getI()
    //@ requires this.B_inv();
    //@ ensures this.B_inv() &*& result == i;
    {
        
        return super.getI();
        
    }
}

class Program {
    public void test(B b) 
    //@ requires b.B_inv();
    //@ ensures b.B_inv();
    {
    	b.getI();
    }
}