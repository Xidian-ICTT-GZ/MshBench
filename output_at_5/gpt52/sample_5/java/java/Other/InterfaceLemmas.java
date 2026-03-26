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
    predicate state(int v) = this.count |-> v;
    @*/

    //@ requires true;
    //@ ensures state(0);
    MyCounter()
        
        
    {
        //@ close state(0);
    }

    //@ requires state(?v);
    //@ ensures state(v) &*& result == v;
    public int get()
        
        
    {
        //@ open state(v);
        int r = count;
        //@ close state(v);
        return r;
        
    }

    //@ requires state(_);
    //@ ensures state(value);
    public void set(int value)
        
        
    {
        
        //@ open state(_);
        count = value;
        //@ close state(value);
        
    }
}

class Program {
    //@ requires c instanceof MyCounter &*& ((MyCounter)c).state(?v);
    //@ ensures c instanceof MyCounter &*& ((MyCounter)c).state(v);
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