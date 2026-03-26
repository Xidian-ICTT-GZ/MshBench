class Thread {

    /*@
    predicate object(Thread this;) = true;
    @*/

    //@ requires true;
    //@ ensures object(this);
    Thread()
    {
    }

    //@ requires object(this);
    //@ ensures false;
    void start()
    {
        throw new NullPointerException();
    }

    //@ requires object(this);
    //@ ensures object(this);
    void run()
    {
    }

    //@ requires object(this);
    //@ ensures false;
    void join()
    {
        throw new NullPointerException();
    }
}

class MyThread extends Thread {

    int x;

    /*@
    predicate object(MyThread this;) =
        this.x |-> _;
    @*/

    //@ requires true;
    //@ ensures object(this);
    MyThread()
    {
        x = 0;
    }

    //@ requires object(this);
    //@ ensures object(this);
    void run()
    {
        //@ open object(this);
        x++;
        //@ close object(this);
    }

    //@ requires object(this);
    //@ ensures object(this) &*& result == x;
    int getResult()
    {
        //@ open object(this);
        int r = x;
        //@ close object(this);
        return r;
    }
}

class Program {

    //@ requires true;
    //@ ensures true;
    public static void main(String[] args)
    {
        MyThread t = new MyThread();
        //@ open t.object();
        t.start();
        t.join();
        int result = t.getResult();
        assert result == 1;
        //@ close t.object();
    }
}