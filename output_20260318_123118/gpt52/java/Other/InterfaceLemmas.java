interface Counter {
    /*@ predicate counter(int v); @*/

    //@ requires counter(?v);
    //@ ensures counter(v) &*& result == v;
    public int get();

    //@ requires counter(?v0);
    //@ ensures counter(value);
    public void set(int value);
}

class MyCounter implements Counter {
    int count;

    /*@ predicate counter(int v) = this.count |-> v; @*/

    //@ requires true;
    //@ ensures counter(0);
    MyCounter()
    {
    }

    //@ requires counter(?v);
    //@ ensures counter(v) &*& result == v;
    public int get()
    {
        return count;
    }

    //@ requires counter(?v0);
    //@ ensures counter(value);
    public void set(int value)
    {
        count = value;
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