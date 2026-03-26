/*@ predicate thread_state(Thread t; int val) = true; @*/

class Thread {

    //@ requires true;
    Thread()
    {
    }

    //@ requires this |-> _;
    //@ ensures true;
    void start()
    {
        throw new NullPointerException();
    }

    //@ requires true;
    //@ ensures true;
    void run()
    {
    }

    //@ requires this |-> _;
    //@ ensures true;
    void join()
    {
        throw new NullPointerException();
    }

}

class MyThread extends Thread {

    int x;

    //@ requires true;
    MyThread()
    {
    }

    //@ requires this |-> x &*& x == 0;
    //@ ensures this |-> x &*& x == 1;
    void run()
    {
        x++;
    }

    //@ requires this |-> x;
    //@ ensures this |-> x &*& result == x;
    int getResult()
    {
        return x;
    }
}

class Program {

    //@ requires true;
    //@ ensures true;
    public static void main(String[] args)
    {
        MyThread t = new MyThread();
        //@ assert t |-> x &*& x == 0;
        t.start();
        t.join();
        int result = t.getResult();
        assert result == 1;
    }

}