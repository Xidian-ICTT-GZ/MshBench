class Thread {

    //@ predicate Thread() = true;
    
    Thread()
    //@ requires true;
    //@ ensures Thread();
    {
    }

    void start()
    //@ requires Thread();
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
    //@ requires Thread();
    //@ ensures true;
    {
        throw new NullPointerException();
    }

}

class MyThread extends Thread {

    int x;
    //@ predicate MyThread() = this.x |-> _ &*& Thread();

    MyThread()
    //@ requires true;
    //@ ensures MyThread();
    {
        //@ close Thread();
        //@ close MyThread();
    }

    void run()
    //@ requires MyThread();
    //@ ensures MyThread();
    {
        //@ open MyThread();
        //@ open Thread();
        x++;
        //@ close Thread();
        //@ close MyThread();
    }

    int getResult()
    //@ requires MyThread();
    //@ ensures MyThread() &*& result == old_x;
    {
        //@ open MyThread();
        int result = x;
        //@ close MyThread();
        return result;
    }
}

class Program {

    public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
    {
        MyThread t = new MyThread();
        //@ assert t.MyThread();
        t.start();
        t.join();
        int result = t.getResult();
        //@ assert result == 0;
        assert result == 1;
    }

}