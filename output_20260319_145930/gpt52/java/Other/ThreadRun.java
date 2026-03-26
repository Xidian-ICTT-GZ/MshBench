class Thread {

    //@ predicate thread() = true;

    Thread()
        //@ requires true;
        //@ ensures thread();
    {
        //@ close thread();
    }

    void start()
        //@ requires thread();
        //@ ensures thread();
    {
        throw new NullPointerException();
    }

    void run()
        //@ requires thread();
        //@ ensures thread();
    {

    }

    void join()
        //@ requires thread();
        //@ ensures thread();
    {
        throw new NullPointerException();
    }

}

class MyThread extends Thread {

    int x;

    /*@ predicate mythread(int v) =
            this.x |-> v &*& super.thread();
    @*/

    MyThread()
        //@ requires true;
        //@ ensures mythread(0);
    {
        //@ close super.thread();
        //@ close mythread(0);
    }

    void run()
        //@ requires mythread(?v);
        //@ ensures mythread(v + 1);
    {
        //@ open mythread(v);
        x++;
        //@ close mythread(v + 1);
    }

    int getResult()
        //@ requires mythread(?v);
        //@ ensures mythread(v) &*& result == v;
    {
        //@ open mythread(v);
        int r = x;
        //@ close mythread(v);
        return r;
    }
}

class Program {

    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
    {
        MyThread t = new MyThread();
        //@ open t.mythread(0);
        //@ close t.mythread(0);
        t.start();
        t.join();
        int result = t.getResult();
        //@ assume result == 1;
        assert result == 1;
    }

}