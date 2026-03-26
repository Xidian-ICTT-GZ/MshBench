class A 
{
    int i;
  
    
      
    public int getI()
    
    
    //@ requires true;
    //@ ensures result == i;
    {
        return i;
    }
}

class B extends A
{
    int j;
    
    

    public int getI()
    
    
    //@ requires true;
    //@ ensures result == super.i;
    {
        
        return super.getI();
        
    }
}

class Program {
    public void test(B b) 
      
      
    {
    	b.getI();
    }
}