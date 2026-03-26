class Thread {

    Thread()
        //@ requires true;
        //@ ensures true;
    {
    }

    void start()
        //@ requires true;
        //@ ensures false;
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
        //@ ensures false;
    {
        throw new NullPointerException();
    }

}

class MyThread extends Thread {

    int x;

    MyThread()
        //@ requires true;
        //@ ensures this.x |-> 0;
    {
        //@ this.x = 0;
    }

    void run()
        //@ requires this.x |-> ?v;
        //@ ensures this.x |-> v + 1;
    {
        x++;
    }

    int getResult()
        //@ requires this.x |-> ?v;
        //@ ensures this.x |-> v &*& result == v;
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