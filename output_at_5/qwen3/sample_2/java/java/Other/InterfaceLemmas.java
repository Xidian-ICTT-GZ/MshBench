interface Counter {
    /*@
    predicate valid(Counter this) = true;
    @*/

    //@ requires this.valid();
    public int get();
        
        

    //@ requires this.valid() &*& value >= 0;
    public void set(int value);
        
        
}

class MyCounter implements Counter {
    int count;

    

    /*@
    predicate valid(MyCounter this) = true;
    @*/

    MyCounter()
        
        
    {
        this.count = 0;
        // Implicitly, the object is in a valid state after construction.
        // No explicit open/close needed for simple initialization if valid is trivial.
    }

    public int get()
        
        
    {
        return count;
        
    }

    public void set(int value)
        
        
    {
        count = value;
        
    }
}

class Program {
    public static void test(Counter c)
        
        
    {
        int value = c.get();
        
        assert 0 <= value;
    }

    public static void main(String[] args)
        
        
    {
        Counter c = new MyCounter();
        c.set(42);
        test(c);
    }
}