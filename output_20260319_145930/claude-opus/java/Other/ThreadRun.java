/*@

predicate_ctor MyThread_pre(MyThread t)() = t.x |-> 0;
predicate_ctor MyThread_post(MyThread t)() = t.x |-> 1;

@*/

class Thread {

    //@ predicate pre();
    //@ predicate post();

    Thread()
        //@ requires true;
        //@ ensures true;
    {
    }

    void start()
        //@ requires pre();
        //@ ensures true;
    {
        throw new NullPointerException();
    }

    void run()
        //@ requires pre();
        //@ ensures post();
    {
    }

    void join()
        //@ requires true;
        //@ ensures post();
    {
        throw new NullPointerException();
    }

}

class MyThread extends Thread {

    int x;

    MyThread()
        //@ requires true;
        //@ ensures MyThread_pre(this)();
    {
        //@ close MyThread_pre(this)();
    }

    //@ predicate pre() = MyThread_pre(this)();
    //@ predicate post() = MyThread_post(this)();

    void run()
        //@ requires pre();
        //@ ensures post();
    {
        //@ open pre();
        //@ open MyThread_pre(this)();
        x++;
        //@ close MyThread_post(this)();
        //@ close post();
    }

    int getResult()
        //@ requires MyThread_post(this)();
        //@ ensures MyThread_post(this)() &*& result == 1;
    {
        //@ open MyThread_post(this)();
        int r = x;
        //@ close MyThread_post(this)();
        return r;
    }
}

class Program {

    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
    {
        MyThread t = new MyThread();
        //@ close t.pre();
        t.start();
        t.join();
        //@ open t.post();
        int result = t.getResult();
        assert result == 1;
    }

}