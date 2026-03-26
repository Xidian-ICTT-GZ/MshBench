interface Counter {
    //@ public invariant true;

    public int get();
        
    public void set(int value);
        
}

/*@
predicate MyCounter_inv(MyCounter c;) = c.count |-> ?count;
@*/
class MyCounter implements Counter {
    int count;

    //@ public instance predicate inv() = MyCounter_inv(this);

    MyCounter()
    //@ requires true;
    //@ ensures inv();
    {
        count = 0;
        //@ close MyCounter_inv(this);
    }

    public int get()
    //@ requires inv();
    //@ ensures inv() &*& result == count;
    {
        return count;
    }

    public void set(int value)
    //@ requires inv();
    //@ ensures inv();
    {
        //@ open MyCounter_inv(this);
        count = value;
        //@ close MyCounter_inv(this);
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