class Thread {

    /*@
    predicate thread_inv() = true;
    @*/

    //@ requires true;
    //@ ensures thread_inv();
    Thread()
    {
    }

    //@ requires thread_inv();
    //@ ensures false;
    void start()
    {
        throw new NullPointerException();
    }

    //@ requires thread_inv();
    //@ ensures thread_inv();
    void run()
    {
    }

    //@ requires thread_inv();
    //@ ensures false;
    void join()
    {
        throw new NullPointerException();
    }

}

class MyThread extends Thread {

    int x;

    /*@
    predicate mythread_inv() = this.thread_inv() &*& x |-> ?v;
    @*/

    //@ requires true;
    //@ ensures mythread_inv() &*& x == 0;
    MyThread()
    {
        x = 0;
    }

    //@ requires mythread_inv();
    //@ ensures mythread_inv() &*& x == old(x) + 1;
    void run()
    {
        //@ open mythread_inv();
        x++;
        //@ close mythread_inv();
    }

    //@ requires mythread_inv();
    //@ ensures mythread_inv() &*& result == x;
    int getResult()
    {
        //@ open mythread_inv();
        int r = x;
        //@ close mythread_inv();
        return r;
    }
}

class Program {

    //@ requires true;
    //@ ensures true;
    public static void main(String[] args)
    {
        MyThread t = new MyThread();
        //@ open t.mythread_inv();
        t.start();
        t.join();
        int result = t.getResult();
        assert result == 1;
        //@ close t.mythread_inv();
    }

}