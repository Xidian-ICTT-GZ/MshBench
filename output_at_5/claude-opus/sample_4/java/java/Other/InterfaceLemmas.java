interface Counter {
    public int get();
    //@ requires true;
    //@ ensures true;

    public void set(int value);
    //@ requires true;
    //@ ensures true;
}

class MyCounter implements Counter {
    int count;
    /*@
    predicate valid() = this.count |-> count;
    @*/

    MyCounter()
    //@ requires true;
    //@ ensures valid() &*& count == 0;
    {
        count = 0;
    }

    public int get()
    //@ requires valid();
    //@ ensures valid() &*& result == count;
    {
        return count;
    }

    public void set(int value)
    //@ requires valid();
    //@ ensures valid() &*& count == value;
    {
        count = value;
    }
}

class Program {
    public static void test(Counter c)
    //@ requires true;
    //@ ensures true;
    {
        int value = c.get();

        assert 0 <= value;
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