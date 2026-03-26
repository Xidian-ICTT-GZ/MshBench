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
    //@ requires c instanceof MyCounter &*& ((MyCounter)c).state();
    //@ ensures c instanceof MyCounter &*& ((MyCounter)c).state();
    public static void test(Counter c)
        
        
    {
        //@ open ((MyCounter)c).state();
        int value = c.get();
        //@ close ((MyCounter)c).state();
        
        assert 0 <= value;
    }

    //@ requires true;
    //@ ensures true;
    public static void main(String[] args)
        
        
    {
        Counter c = new MyCounter();
        //@ open ((MyCounter)c).state();
        c.set(42);
        //@ close ((MyCounter)c).state();
        test(c);
    }
}