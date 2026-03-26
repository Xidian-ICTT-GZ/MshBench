interface Counter {
    
    //@ requires true;
    //@ ensures true;
    public int get();
        
        

    //@ requires true;
    //@ ensures true;
    public void set(int value);
        
        
}

class MyCounter implements Counter {
    int count;

    /*@
    predicate inv() = this.count |-> ?c;
    @*/

    //@ requires this.inv();
    //@ ensures this.inv();
    MyCounter()
        
        
    {
        //@ close inv();
    }

    //@ requires this.inv();
    //@ ensures this.inv() &*& result == ?r;
    public int get()
        
        
    {
        //@ open inv();
        int r = count;
        //@ close inv();
        return r;
        
    }

    //@ requires this.inv();
    //@ ensures this.inv();
    public void set(int value)
        
        
    {
        //@ open inv();
        count = value;
        //@ close inv();
        
    }
}

class Program {
    //@ requires true;
    //@ ensures true;
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