interface Counter {
    

    public int get();
        
        

    public void set(int value);
        
        
}

class MyCounter implements Counter {
    int count;

    /*@
    predicate state() = this.count |-> ?c;
    @*/

    //@ requires true;
    //@ ensures state();
    MyCounter()
        
        
    {
        //@ close state();
    }

    //@ requires state();
    //@ ensures state();
    public int get()
        
        
    {
        //@ open state();
        int res = count;
        //@ close state();
        return count;
        
    }

    //@ requires state();
    //@ ensures state();
    public void set(int value)
        
        
    {
        
        //@ open state();
        count = value;
        //@ close state();
    }
}

class Program {
    //@ requires true;
    //@ ensures true;
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