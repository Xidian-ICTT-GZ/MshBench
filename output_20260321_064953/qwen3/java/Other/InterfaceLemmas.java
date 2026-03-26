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
    predicate MyCounter_own() = this.count |-> _;
    @*/

    //@ requires true;
    //@ ensures MyCounter_own();
    MyCounter()
    {
        //@ close MyCounter_own();
    }

    //@ requires MyCounter_own();
    //@ ensures MyCounter_own() &*& result == this.count;
    public int get()
    {
        //@ open MyCounter_own();
        //@ close MyCounter_own();
        return count;
    }

    //@ requires MyCounter_own();
    //@ ensures MyCounter_own();
    public void set(int value)
    {
        //@ open MyCounter_own();
        count = value;
        //@ close MyCounter_own();
    }
}

class Program {
    //@ requires Counter_own(c);
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