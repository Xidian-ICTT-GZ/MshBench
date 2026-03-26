class A 
{
    int i;
  
    //@ predicate A() = this.i |-> _;
    
      
    public int getI()
    //@ requires A();
    //@ ensures A();
    
    {
        return i;
    }
}

class B extends A
{
    int j;
    
    //@ predicate B() = this.A() &*& this.j |-> _;

    public int getI()
    //@ requires B();
    //@ ensures B();
    
    {
        //@ open B();
        //@ close A();
        return super.getI();
        //@ close B();
    }
}

class Program {
    public void test(B b) 
    //@ requires b != null &*& b.B();
    //@ ensures b.B();
      
      
    {
    	b.getI();
    }
}