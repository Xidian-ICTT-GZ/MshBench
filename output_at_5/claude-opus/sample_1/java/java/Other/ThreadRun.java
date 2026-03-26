class Thread {

/*@
  predicate this_inv() = true;
@*/
    Thread()
    //@ requires true;
    //@ ensures this_inv();
    {
    }

    void start()
    //@ requires this_inv();
    //@ ensures this_inv();
    {
        throw new NullPointerException();
    }

    void run()
    //@ requires this_inv();
    //@ ensures this_inv();
    {
    }

    void join()
    //@ requires this_inv();
    //@ ensures this_inv();
    {
        throw new NullPointerException();
    }

}

class MyThread extends Thread {

    int x;

/*@
  predicate this_inv() = this.x |-> _;
@*/
    MyThread()
    //@ requires true;
    //@ ensures this_inv();
    {
    }

    void run()
    //@ requires this_inv();
    //@ ensures this_inv();
    {
        //@ open this_inv();
        x++;
        //@ close this_inv();
    }

    int getResult()
    //@ requires this_inv();
    //@ ensures this_inv() &*& result == x;
    {
        //@ open this_inv();
        int r = x;
        //@ close this_inv();
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