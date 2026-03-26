class A 
{
    int i;
  
    
      
    public int getI()
    
    
    {
        return i;
    }
}


class B extends A
{
    int j;
    
    

    public int getI()
    
    
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