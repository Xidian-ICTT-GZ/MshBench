/*@ predicate A(int i) = this.i |-> i; @*/
/*@ predicate B(int i, int j) = A(i) &*& this.j |-> j; @*/

class A 
{
    int i;
  
    
      
    //@ requires A(?i);
    //@ ensures result == i;
    public int getI()
    {
        return i;
    }
}

class B extends A
{
    int j;
    
    

    //@ requires B(?i, ?j);
    //@ ensures result == i;
    public int getI()
    {
        
        return super.getI();
        
    }
}

class Program {
    //@ requires B(?i, ?j);
    //@ ensures true;
    public void test(B b) 
    {
    	b.getI();
    }
}