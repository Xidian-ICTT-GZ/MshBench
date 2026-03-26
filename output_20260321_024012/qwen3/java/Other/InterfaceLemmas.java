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
    predicate valid() = true;
    @*/

    //@ requires true;
    //@ ensures valid();
    MyCounter()
    {
        //@ close valid();
    }

    //@ requires valid();
    //@ ensures valid() &*& result == count;
    public int get()
    {
        return count;
    }

    //@ requires valid();
    //@ ensures valid();
    public void set(int value)
    {
        count = value;
    }
}

class Program {
    //@ requires true;
    //@ ensures true;
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