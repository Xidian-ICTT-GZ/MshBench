class A 
{
    int i;
  
    /*@
    predicate inv() = this.i |-> ?v;
    @*/
      
    public int getI()
    
    
    //@ requires inv();
    //@ ensures inv() &*& result == i;
    {
        return i;
    }
}

class B extends A
{
    int j;
    
    /*@
    predicate invB() = this.j |-> ?w &*& this.inv();
    @*/
    

    public int getI()
    
    
    //@ requires invB();
    //@ ensures invB() &*& result == i;
    {
        
        return super.getI();
        
    }
}

class Program {
    public void test(B b) 
      
      
    //@ requires b != null &*& b.invB();
    //@ ensures b.invB();
    {
    	b.getI();
    }
}