class A 
{
    int i;
  
    
      
    public int getI()
    //@ requires true;
    //@ ensures true;
    
    
    {
        return i;
    }
}

class B extends A
{
    int j;
    
    

    public int getI()
    //@ requires true;
    //@ ensures true;
    
    
    {
        
        return super.getI();
        
    }
}

class Program {
    public void test(B b) 
    //@ requires true;
    //@ ensures true;
      
      
    {
    	b.getI();
    }
}