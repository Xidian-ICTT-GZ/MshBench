interface Counter {
    /*@
    predicate counter(int v);
    @*/

    //@ requires counter(?v);
    //@ ensures counter(v) &*& result == v;
    public int get();

    //@ requires counter(_);
    //@ ensures counter(value);
    public void set(int value);
}

class MyCounter implements Counter {
    int count;

    /*@
    predicate counter(int v) = this.count |-> v;
    @*/

    //@ requires true;
    //@ ensures counter(0);
    MyCounter()
    {
        //@ close counter(0);
    }

    //@ requires counter(?v);
    //@ ensures counter(v) &*& result == v;
    public int get()
    {
        //@ open counter(v);
        int r = count;
        //@ close counter(v);
        return r;
    }

    //@ requires counter(_);
    //@ ensures counter(value);
    public void set(int value)
    {
        //@ open counter(_);
        count = value;
        //@ close counter(value);
    }
}

class Program {
    //@ requires c.counter(?v) &*& 0 <= v;
    //@ ensures c.counter(v);
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