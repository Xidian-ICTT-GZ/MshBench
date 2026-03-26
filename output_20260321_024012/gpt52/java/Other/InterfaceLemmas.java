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
    predicate inv() = this.count |-> ?c;
    @*/

    //@ requires true;
    //@ ensures inv();
    MyCounter()
        
        
    {
        //@ close inv();
    }

    //@ requires inv();
    //@ ensures inv() &*& result == count;
    public int get()
        
        
    {
        //@ open inv();
        int result = count;
        //@ close inv();
        return result;
        
    }

    //@ requires inv();
    //@ ensures inv();
    public void set(int value)
        
        
    {
        //@ open inv();
        count = value;
        //@ close inv();
        
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