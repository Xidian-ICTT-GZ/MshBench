class Thread {

    /*@
    predicate Thread_state() = true;
    @*/

    Thread()
        //@ requires true;
        //@ ensures Thread_state();
    {
        //@ close Thread_state();
    }

    void start()
        //@ requires Thread_state();
        //@ ensures Thread_state();
    {
        throw new NullPointerException();
    }

    void run()
        //@ requires Thread_state();
        //@ ensures Thread_state();
    {
    }

    void join()
        //@ requires Thread_state();
        //@ ensures Thread_state();
    {
        throw new NullPointerException();
    }

}

class MyThread extends Thread {

    int x;

    /*@
    predicate MyThread_state(int v) = this.x |-> v;
    @*/

    MyThread()
        //@ requires true;
        //@ ensures MyThread_state(0);
    {
        //@ close MyThread_state(0);
    }

    void run()
        //@ requires MyThread_state(?v);
        //@ ensures MyThread_state(v + 1);
    {
        //@ open MyThread_state(v);
        x++;
        //@ close MyThread_state(v + 1);
    }

    int getResult()
        //@ requires MyThread_state(?v);
        //@ ensures MyThread_state(v) &*& result == v;
    {
        //@ open MyThread_state(v);
        int r = x;
        //@ close MyThread_state(v);
        return r;
    }
}

class Program {

    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
    {
        MyThread t = new MyThread();
        //@ open t.MyThread_state(?v0);
        //@ close t.MyThread_state(v0);
        t.start();
        //@ open t.MyThread_state(?v1);
        //@ close t.MyThread_state(v1);
        t.join();
        //@ open t.MyThread_state(?v2);
        //@ close t.MyThread_state(v2);
        int result = t.getResult();
        assert result == 1;
    }

}