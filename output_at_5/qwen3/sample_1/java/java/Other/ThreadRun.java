class Thread {

    //@ predicate thread(Thread t) = true;
    
    Thread()
        //@ ensures thread(this);
    {
    }

    void start()
        //@ requires thread(this);
        //@ ensures thread(this);
    {
        throw new NullPointerException();
    }

    void run()
        //@ requires thread(this);
        //@ ensures thread(this);
    {
        
        
    }

    void join()
        //@ requires thread(this);
        //@ ensures thread(this);
    {
        throw new NullPointerException();
    }

}

class MyThread extends Thread {

    int x;

    /*@
    predicate myThread(MyThread m, int val) = thread(m) &*& m.x == val;
    @*/

    MyThread()
        //@ ensures myThread(this, 0);
    {
        
    }

    void run()
        //@ requires myThread(this, ?oldVal);
        //@ open myThread(this, oldVal);
        //@ ensures myThread(this, oldVal + 1);
        //@ close myThread(this, oldVal + 1);
    {
        
        x++;
        
    }

    int getResult()
        //@ requires myThread(this, ?val);
        //@ open myThread(this, val);
        //@ ensures result == val &*& myThread(this, val);
        //@ close myThread(this, val);
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