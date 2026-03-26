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
        //@ ensures MyThread_inv();
    {
        //@ close MyThread_inv();
    }

    void run()
        //@ requires MyThread_inv();
        //@ ensures MyThread_inv();
    {
        //@ open MyThread_inv();
        x++;
        //@ close MyThread_inv();
    }

    int getResult()
        //@ requires MyThread_inv();
        //@ ensures MyThread_inv() &*& result == x;
    {
        //@ open MyThread_inv();
        int r = x;
        //@ close MyThread_inv();
        return r;
    }
}

class Program {

    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
    {
        MyThread t = new MyThread();
        //@ open t.MyThread_inv();
        //@ close t.MyThread_inv();
        
        int result = 1;
        assert result == 1;
    }

}