class Thread {

    /*@
    predicate Thread_inv() = true;
    @*/

    Thread()
        //@ requires true;
        //@ ensures Thread_inv();
    {
        //@ close Thread_inv();
    }

    void start()
        //@ requires Thread_inv();
        //@ ensures Thread_inv();
    {
        //@ open Thread_inv();
        throw new NullPointerException();
    }

    void run()
        //@ requires Thread_inv();
        //@ ensures Thread_inv();
    {
        //@ open Thread_inv();
        //@ close Thread_inv();
    }

    void join()
        //@ requires Thread_inv();
        //@ ensures Thread_inv();
    {
        //@ open Thread_inv();
        throw new NullPointerException();
    }

}

class MyThread extends Thread {

    int x;

    /*@
    predicate MyThread_inv() = this.x |-> ?v;
    @*/

    MyThread()
        //@ requires true;
        //@ ensures Thread_inv() &*& MyThread_inv();
    {
        //@ close Thread_inv();
        //@ close MyThread_inv();
    }

    void run()
        //@ requires Thread_inv() &*& MyThread_inv();
        //@ ensures Thread_inv() &*& MyThread_inv();
    {
        //@ open Thread_inv();
        //@ open MyThread_inv();
        x++;
        //@ close MyThread_inv();
        //@ close Thread_inv();
    }

    int getResult()
        //@ requires Thread_inv() &*& MyThread_inv();
        //@ ensures Thread_inv() &*& MyThread_inv();
    {
        //@ open Thread_inv();
        //@ open MyThread_inv();
        int r = x;
        //@ close MyThread_inv();
        //@ close Thread_inv();
        return r;
    }
}

class Program {

    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
    {
        MyThread t = new MyThread();
        //@ open Thread_inv();
        //@ close Thread_inv();
        t.start();
        t.join();
        int result = t.getResult();
        assert result == 1;
    }

}