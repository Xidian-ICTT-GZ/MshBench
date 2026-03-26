interface Counter {
    //@ predicate CounterState(int value);
    
    public int get();
    //@ requires CounterState(?value);
    //@ ensures CounterState(value) &*& result == value;
        
    public void set(int value);
    //@ requires CounterState(_);
    //@ ensures CounterState(value);
}

class MyCounter implements Counter {
    int count;
    
    //@ predicate CounterState(int value) = count |-> value;
    
    MyCounter()
    //@ requires true;
    //@ ensures CounterState(0);
    {
        //@ close CounterState(0);
    }

    public int get()
    //@ requires CounterState(?value);
    //@ ensures CounterState(value) &*& result == value;
    {
        //@ open CounterState(value);
        return count;
        //@ close CounterState(value);
    }

    public void set(int value)
    //@ requires CounterState(_);
    //@ ensures CounterState(value);
    {
        //@ open CounterState(_);
        count = value;
        //@ close CounterState(value);
    }
}

class Program {
    public static void test(Counter c)
    //@ requires c.CounterState(?value);
    //@ ensures c.CounterState(value);
    {
        int value = c.get();
        //@ assert 0 <= value;
    }

    public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
    {
        Counter c = new MyCounter();
        c.set(42);
        test(c);
    }
}