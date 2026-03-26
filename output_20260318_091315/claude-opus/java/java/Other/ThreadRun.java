class Thread {

    //@ predicate thread_inv() = true;

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

    int x;

    //@ predicate mythread_inv(MyThread this) = this.x |-> _ &*& thread_inv();

    MyThread()
        //@ requires true;
        //@ ensures mythread_inv(this);
    {
    }

    void run()
        //@ requires mythread_inv(this);
        //@ ensures mythread_inv(this) &*& x == old(x) + 1;
    {
        x++;
    }

    int getResult()
        //@ requires mythread_inv(this);
        //@ ensures mythread_inv(this) &*& result == x;
    {
        return x;
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