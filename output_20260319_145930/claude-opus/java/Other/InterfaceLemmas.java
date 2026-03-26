interface Counter {
    //@ predicate Counter(int v);

    public int get();
        //@ requires Counter(?v) &*& 0 <= v;
        //@ ensures Counter(v) &*& result == v;

    public void set(int value);
        //@ requires Counter(_) &*& 0 <= value;
        //@ ensures Counter(value);
}

class MyCounter implements Counter {
    int count;

    /*@
    predicate Counter(int v) = this.count |-> v;
    @*/

    MyCounter()
        //@ requires true;
        //@ ensures Counter(0);
    {
        //@ close Counter(0);
    }

    public int get()
        //@ requires Counter(?v) &*& 0 <= v;
        //@ ensures Counter(v) &*& result == v;
    {
        //@ open Counter(v);
        return count;
        //@ close Counter(count);
    }

    public void set(int value)
        //@ requires Counter(_) &*& 0 <= value;
        //@ ensures Counter(value);
    {
        //@ open Counter(_);
        count = value;
        //@ close Counter(value);
    }
}

class Program {
    public static void test(Counter c)
        //@ requires c.Counter(?v) &*& 0 <= v;
        //@ ensures c.Counter(v);
    {
        int value = c.get();
        //@ assert 0 <= value;
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