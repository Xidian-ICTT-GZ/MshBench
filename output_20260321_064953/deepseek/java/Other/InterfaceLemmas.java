interface Counter {
    //@ predicate CounterState(int value);

    //@ requires CounterState(?value);
    //@ ensures CounterState(value) &*& result == value;
    public int get();

    //@ requires CounterState(_);
    //@ ensures CounterState(value);
    public void set(int value);
}

class MyCounter implements Counter {
    int count;

    //@ predicate CounterState(int value) = count |-> value;

    //@ ensures CounterState(0);
    MyCounter()
    {
        //@ close CounterState(0);
    }

    //@ requires CounterState(?value);
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
    //@ requires c.CounterState(?value);
    //@ ensures c.CounterState(value);
    public static void test(Counter c)
    {
        int value = c.get();
        //@ assert 0 <= value;
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