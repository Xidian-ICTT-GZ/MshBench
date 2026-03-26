class Thread {

/*@
  predicate this_inv(Thread this) = true;
@*/
    Thread()
    //@ requires true;
    //@ ensures this_inv(this);
    {
    }

    void start()
    //@ requires this_inv(this);
    //@ ensures this_inv(this);
    {
        throw new NullPointerException();
    }

    void run()
    //@ requires this_inv(this);
    //@ ensures this_inv(this);
    {
    }

    void join()
    //@ requires this_inv(this);
    //@ ensures this_inv(this);
    {
        throw new NullPointerException();
    }

}

class MyThread extends Thread {

    int x;

/*@
  predicate this_inv(MyThread this) = this.x |-> _;
@*/
    MyThread()
    //@ requires true;
    //@ ensures this_inv(this);
    {
        x = 0;
    }

    void run()
    //@ requires this_inv(this);
    //@ ensures this_inv(this);
    {
        //@ open this_inv(this);
        x++;
        //@ close this_inv(this);
    }

    int getResult()
    //@ requires this_inv(this);
    //@ ensures this_inv(this) &*& result == x;
    {
        //@ open this_inv(this);
        int r = x;
        //@ close this_inv(this);
        return r;
    }
}

class Program {

    public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
    {
        MyThread t = new MyThread();
        t.start();
        t.join();
        int result = t.getResult();
        assert result == 1;
    }

}