class Thread {

    /*@
    predicate thread_inv() = true;
    @*/

    Thread()
        //@ requires true;
        //@ ensures thread_inv();
    {
        //@ close thread_inv();
    }

    void start()
        //@ requires thread_inv();
        //@ ensures thread_inv();
    {
        //@ open thread_inv();
        throw new NullPointerException();
    }

    void run()
        //@ requires thread_inv();
        //@ ensures thread_inv();
    {
        //@ open thread_inv();
        //@ close thread_inv();
    }

    void join()
        //@ requires thread_inv();
        //@ ensures thread_inv();
    {
        //@ open thread_inv();
        throw new NullPointerException();
    }

}

class MyThread extends Thread {

    int x;

    /*@
    predicate mythread_inv(int v) = this.x |-> v &*& thread_inv();
    @*/

    MyThread()
        //@ requires true;
        //@ ensures mythread_inv(0);
    {
        //@ close thread_inv();
        //@ close mythread_inv(0);
    }

    void run()
        //@ requires mythread_inv(?v);
        //@ ensures mythread_inv(v + 1);
    {
        //@ open mythread_inv(v);
        x++;
        //@ close mythread_inv(v + 1);
    }

    int getResult()
        //@ requires mythread_inv(?v);
        //@ ensures mythread_inv(v) &*& result == v;
    {
        //@ open mythread_inv(v);
        int r = x;
        //@ close mythread_inv(v);
        return r;
    }
}

class Program {

    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
    {
        MyThread t = new MyThread();
        //@ open t.mythread_inv(0);
        //@ close t.mythread_inv(0);
        t.start();
        t.join();
        int result = t.getResult();
        assert result == 1;
    }

}