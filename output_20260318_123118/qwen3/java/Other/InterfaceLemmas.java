/*@ predicate counter(Counter c, int v) = 
    c instanceof MyCounter &*& 
    MyCounter_count(c, v); @*/

/*@ predicate MyCounter_count(MyCounter mc, int v) = 
    mc.count |-> v; @*/

interface Counter {

    //@ requires counter(this, _);
    //@ ensures counter(this, result);
    public int get();
    
    //@ requires true;
    //@ ensures counter(this, value);
    public void set(int value);
    
}

class MyCounter implements Counter {
    int count;

    //@ ensures counter(this, 0);
    MyCounter() {
    }

    //@ requires counter(this, v) &*& 0 <= v;
    //@ ensures counter(this, v) &*& result == v;
    public int get() {
        return count;
    }

    //@ requires true;
    //@ ensures counter(this, value);
    public void set(int value) {
        count = value;
    }
}

class Program {
    //@ requires counter(c, v) &*& 0 <= v;
    //@ ensures true;
    public static void test(Counter c) {
        int value = c.get();
        assert 0 <= value;
    }

    //@ requires true;
    //@ ensures true;
    public static void main(String[] args) {
        Counter c = new MyCounter();
        c.set(42);
        test(c);
    }
}