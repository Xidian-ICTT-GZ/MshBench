interface Counter {
    









    public int get();
        
        

    public void set(int value);
        
        
}

class MyCounter implements Counter {
    int count;

    













    MyCounter()
        
        
    {
        
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