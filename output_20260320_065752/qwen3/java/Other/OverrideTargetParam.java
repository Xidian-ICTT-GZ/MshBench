class A 
{
    int i;
  
    
      
    //@ requires this |-> i _;
    //@ ensures result == i;
    public int getI()
    
    
    {
        return i;
    }
}

class B extends A
{
    int j;
    
    

    //@ requires this |-> i _ &*& this |-> j _;
    //@ ensures result == i;
    public int getI()
    
    
    {
        
        return super.getI();
        
    }
}

class Program {
    //@ requires b |-> i _ &*& b |-> j _;
    //@ ensures true;
    public void test(B b) 
      
      
    {
    	b.getI();
    }
}