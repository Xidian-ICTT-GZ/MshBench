class A 
{
    int i;
  
    /*@
    predicate A_inv() = this.i |-> _;
    @*/
      
    public int getI()
    //@ requires A_inv();
    //@ ensures A_inv();
    {
        //@ open A_inv();
        int result = i;
        //@ close A_inv();
        return result;
    }
}

class B extends A
{
    int j;
    
    /*@
    predicate B_inv() = this.A_inv() &*& this.j |-> _;
    @*/

    public int getI()
    //@ requires B_inv();
    //@ ensures B_inv();
    {
        //@ open B_inv();
        int result = super.getI();
        //@ close B_inv();
        return result;
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