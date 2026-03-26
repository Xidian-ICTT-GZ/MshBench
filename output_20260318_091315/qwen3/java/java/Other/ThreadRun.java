//@ predicate thread_state(Thread t; int x) = true;

class Thread {

    //@ requires true;
    Thread()
    {
    }

    //@ requires true;
    void start()
    {
        throw new NullPointerException();
    }

    //@ requires true;
    void run()
    {
    }

    //@ requires true;
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

    //@ requires this.x |-> ?old_x &*& old_x == 0;
    //@ ensures this.x |-> old_x + 1;
    void run()
    {
        x++;
    }

    //@ requires this.x |-> ?val;
    //@ ensures this.x |-> val &*& result == val;
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
        //@ close t.x |-> 0;
        t.start();
        t.join();
        int result = t.getResult();
        assert result == 1;
    }

}