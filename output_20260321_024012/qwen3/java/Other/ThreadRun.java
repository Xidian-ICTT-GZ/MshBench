/*@ predicate Thread_own(Thread t) = true; @*/
/*@ predicate MyThread_own(MyThread t) = t.x |-> ?x &*& Thread_own(t); @*/

class Thread {

    //@ requires true;
    //@ ensures Thread_own(this);
    Thread()
    {
        //@ close Thread_own(this);
    }

    //@ requires Thread_own(this);
    //@ ensures true;
    void start()
    {
        throw new NullPointerException();
    }

    //@ requires Thread_own(this);
    //@ ensures true;
    void run()
    {
    }

    //@ requires Thread_own(this);
    //@ ensures true;
    void join()
    {
        throw new NullPointerException();
    }

}

class MyThread extends Thread {

    int x;

    //@ requires true;
    //@ ensures MyThread_own(this);
    MyThread()
    {
        x = 0;
        //@ close MyThread_own(this);
    }

    //@ requires MyThread_own(this);
    //@ ensures MyThread_own(this);
    void run()
    {
        //@ open MyThread_own(this);
        x++;
        //@ close MyThread_own(this);
    }

    //@ requires MyThread_own(this);
    //@ ensures MyThread_own(this) &*& result == this.x;
    int getResult()
    {
        //@ open MyThread_own(this);
        int tmp = x;
        //@ close MyThread_own(this);
        return tmp;
    }
}

class Program {

    //@ requires true;
    //@ ensures true;
    public static void main(String[] args)
    {
        MyThread t = new MyThread();
        t.start();
        t.join();
        int result = t.getResult();
        assert result == 1;
    }

}