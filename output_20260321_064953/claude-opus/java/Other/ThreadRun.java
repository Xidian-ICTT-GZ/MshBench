class Thread {

/*@
  predicate thread_inv() = true;
@*/

    Thread()
    //@ requires true;
    //@ ensures thread_inv();
    {
    }

    void start()
    //@ requires thread_inv();
    //@ ensures thread_inv();
    {
        throw new NullPointerException();
    }

    void run()
    //@ requires thread_inv();
    //@ ensures thread_inv();
    {
    }

    void join()
    //@ requires thread_inv();
    //@ ensures thread_inv();
    {
        throw new NullPointerException();
    }

}

class MyThread extends Thread {

/*@
  predicate mythread_inv(MyThread this) = this.thread_inv() &*& this.x |-> ?x;
@*/

    int x;

    MyThread()
    //@ requires true;
    //@ ensures mythread_inv(this);
    {
        x = 0;
    }

    void run()
    //@ requires mythread_inv(this);
    //@ ensures mythread_inv(this);
    {
        //@ open mythread_inv(this);
        x++;
        //@ close mythread_inv(this);
    }

    int getResult()
    //@ requires mythread_inv(this);
    //@ ensures mythread_inv(this) &*& result == x;
    {
        //@ open mythread_inv(this);
        int r = x;
        //@ close mythread_inv(this);
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