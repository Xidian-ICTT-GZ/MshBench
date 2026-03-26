interface Counter {
    //@ requires true;
    public int get();
        
    //@ requires true;
    public void set(int value);
        
        
}

class MyCounter implements Counter {
    int count;

    /*@
    predicate MyCounter_own() = true;
    @*/

    //@ requires true;
    //@ ensures MyCounter_own();
    MyCounter()
    {
        //@ close MyCounter_own();
    }

    //@ requires MyCounter_own();
    //@ ensures MyCounter_own() &*& result == count;
    public int get()
    {
        return count;
    }

    //@ requires MyCounter_own();
    //@ ensures MyCounter_own();
    public void set(int value)
    {
        count = value;
    }
}

class Program {
    //@ requires Counter c &*& c instanceof MyCounter ? MyCounter_own() : true;
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