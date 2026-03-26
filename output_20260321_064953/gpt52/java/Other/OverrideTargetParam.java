class A 
{
    int i;
  
    /*@
    predicate a_state(int v) = this.i |-> v;
    @*/
      
    public int getI()
    //@ requires this.a_state(?v);
    //@ ensures this.a_state(v) &*& result == v;
    {
        return i;
    }
}

class B extends A
{
    int j;
    
    /*@
    predicate b_state(int v, int w) = this.a_state(v) &*& this.j |-> w;
    @*/

    public int getI()
    //@ requires this.b_state(?v, ?w);
    //@ ensures this.b_state(v, w) &*& result == v;
    {
        //@ open b_state(v, w);
        int r = super.getI();
        //@ close b_state(v, w);
        return r;
        
    }
}

class Program {
    public void test(B b) 
    //@ requires b.b_state(?v, ?w);
    //@ ensures b.b_state(v, w);
    {
    	b.getI();
    }
}