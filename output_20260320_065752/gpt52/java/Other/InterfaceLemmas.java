interface Counter {
    /*@
    predicate Counter_inv() = true;
    @*/

    //@ requires this.Counter_inv();
    //@ ensures this.Counter_inv() &*& result >= 0;
    public int get();
        
        

    //@ requires this.Counter_inv();
    //@ ensures this.Counter_inv();
    public void set(int value);
        
        
}

class MyCounter implements Counter {
    int count;

    /*@
    predicate Counter_inv() = this.count |-> ?v &*& v >= 0;
    @*/

    //@ requires true;
    //@ ensures this.Counter_inv();
    MyCounter()
        
        
    {
        //@ close Counter_inv();
    }

    //@ requires this.Counter_inv();
    //@ ensures this.Counter_inv() &*& result >= 0;
    public int get()
        
        
    {
        //@ open Counter_inv();
        int result = count;
        //@ close Counter_inv();
        return result;
        
    }

    //@ requires this.Counter_inv();
    //@ ensures this.Counter_inv();
    public void set(int value)
        
        
    {
        //@ open Counter_inv();
        count = value;
        //@ close Counter_inv();
        
    }
}

class Program {
    //@ requires c.Counter_inv();
    //@ ensures c.Counter_inv();
    public static void test(Counter c)
        
        
    {
        int value = c.get();
        
        assert 0 <= value;
    }

    //@ requires true;
    //@ ensures true;
    public static void main(String[] args)
        
        
    {
        Counter c = new MyCounter();
        c.set(42);
        test(c);
    }
}