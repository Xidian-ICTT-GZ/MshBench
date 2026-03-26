interface Counter {
    //@ predicate CounterState(int value);
    
    //@ requires CounterState(value);
    //@ ensures CounterState(value) &*& result == value;
    public int get();
        
    //@ requires CounterState(_);
    //@ ensures CounterState(value);
    public void set(int value);
        
        
}

class MyCounter implements Counter {
    int count;
    //@ predicate CounterState(int value) = this.count |-> value;

    //@ ensures CounterState(0);
    MyCounter()
    {
        //@ close CounterState(0);
    }

    //@ requires CounterState(value);
    //@ ensures CounterState(value) &*& result == value;
    public int get()
    {
        //@ open CounterState(value);
        return count;
        //@ close CounterState(value);
    }

    //@ requires CounterState(_);
    //@ ensures CounterState(value);
    public void set(int value)
    {
        //@ open CounterState(_);
        count = value;
        //@ close CounterState(value);
    }
}

class Program {
    //@ requires c.CounterState(value) &*& 0 <= value;
    //@ ensures c.CounterState(value);
    public static void test(Counter c)
    {
        //@ open c.CounterState(value);
        int value = c.get();
        //@ close c.CounterState(value);
        assert 0 <= value;
    }

    public static void main(String[] args)
    {
        Counter c = new MyCounter();
        //@ close c.CounterState(0);
        c.set(42);
        //@ open c.CounterState(0);
        //@ close c.CounterState(42);
        //@ assert c.CounterState(42);
        //@ close c.CounterState(42) &*& 0 <= 42;
        test(c);
    }
}