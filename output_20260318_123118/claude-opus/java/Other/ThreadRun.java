class Thread {

    //@ predicate thread_object(Thread t) = true;

    Thread()
        //@ requires true;
        //@ ensures thread_object(this);
    {
    }

    void start()
        //@ requires thread_object(this);
        //@ ensures thread_object(this);
    {
        throw new NullPointerException();
    }

    void run()
        //@ requires thread_object(this);
        //@ ensures thread_object(this);
    {
        
    }

    void join()
        //@ requires thread_object(this);
        //@ ensures thread_object(this);
    {
        throw new NullPointerException();
    }

}

class MyThread extends Thread {

    int x;

    //@ predicate mythread_object(MyThread t, int val) = thread_object(t) &*& t.x |-> val;

    MyThread()
        //@ requires true;
        //@ ensures mythread_object(this, 0);
    {
    }

    void run()
        //@ requires mythread_object(this, ?v);
        //@ ensures mythread_object(this, v + 1);
    {
        x++;
    }

    int getResult()
        //@ requires mythread_object(this, ?v);
        //@ ensures mythread_object(this, v) &*& result == v;
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
        //@ open mythread_object(t, ?v);
        //@ close mythread_object(t, v);
        assert result == 1;
    }
}