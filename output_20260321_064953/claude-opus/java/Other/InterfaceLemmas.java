interface Counter {
    //@ public invariant true;

    //@ requires true;
    //@ ensures true;
    public int get();

    //@ requires true;
    //@ ensures true;
    public void set(int value);

}

/*@
predicate mycounter_inv(MyCounter this) = 
  this.count |-> _;
@*/
class MyCounter implements Counter {
    int count;

    //@ requires true;
    //@ ensures mycounter_inv(this);
    MyCounter() 
    {
        //@ close mycounter_inv(this);
    }

    //@ requires mycounter_inv(this);
    //@ ensures mycounter_inv(this) &*& result == this.count;
    public int get()
    {
        //@ open mycounter_inv(this);
        return count;
        //@ close mycounter_inv(this);
    }

    //@ requires mycounter_inv(this);
    //@ ensures mycounter_inv(this);
    public void set(int value)
    {
        //@ open mycounter_inv(this);
        count = value;
        //@ close mycounter_inv(this);
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