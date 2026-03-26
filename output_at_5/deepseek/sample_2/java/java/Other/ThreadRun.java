class Thread {

    
    

    Thread()
        //@ requires true;
        //@ ensures true;
    {
    }

    void start()
        //@ requires true;
        //@ ensures true;
    {
        throw new NullPointerException();
    }

    void run()
        //@ requires true;
        //@ ensures true;
    {
        
        
    }

    void join()
        //@ requires true;
        //@ ensures true;
    {
        throw new NullPointerException();
    }

}

class MyThread extends Thread {

    int x;

    MyThread()
        //@ requires true;
        //@ ensures MyThread_x(this, 0);
    {
        //@ close MyThread_x(this, 0);
    }

    
    

    void run()
        //@ requires MyThread_x(this, ?v);
        //@ ensures MyThread_x(this, v + 1);
    {
        //@ open MyThread_x(this, v);
        x++;
        //@ close MyThread_x(this, v + 1);
    }

    int getResult()
        //@ requires MyThread_x(this, ?v);
        //@ ensures MyThread_x(this, v) &*& result == v;
    {
        //@ open MyThread_x(this, v);
        int r = x;
        //@ close MyThread_x(this, v);
        return r;
    }
}

/*@
predicate MyThread_x(MyThread t; int v) = t.x |-> v;
@*/

class Program {

    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
    {
        MyThread t = new MyThread();
        t.start();
        t.join();
        //@ open MyThread_x(t, ?v);
        int result = t.getResult();
        //@ close MyThread_x(t, v);
        //@ assert result == v;
    }

}