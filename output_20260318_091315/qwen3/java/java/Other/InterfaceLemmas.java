/*@ predicate Counter(Counter c; int v) = 
    c instanceof MyCounter &*& 
    MyCounter(c, v);
@*/

/*@ predicate MyCounter(MyCounter mc; int v) = 
    mc.count |-> v;
@*/

interface Counter {

//@ requires Counter(this, ?v);
//@ ensures result == v;
public int get();

//@ requires Counter(this, ?old_v) &*& value >= 0;
//@ ensures Counter(this, value);
public void set(int value);

}

class MyCounter implements Counter {
    int count;

//@ requires true;
//@ ensures MyCounter(this, 0);
    MyCounter()
    {
    }

//@ requires MyCounter(this, ?v);
//@ ensures result == v &*& MyCounter(this, v);
    public int get()
    {
        return count;
    }

//@ requires MyCounter(this, ?old_v) &*& value >= 0;
//@ ensures MyCounter(this, value);
    public void set(int value)
    {
        count = value;
    }
}

class Program {
//@ requires c != null &*& Counter(c, ?v) &*& v >= 0;
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