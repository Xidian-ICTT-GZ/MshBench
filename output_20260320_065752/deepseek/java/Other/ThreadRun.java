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
        //@ ensures this.x |-> 0;
    {
        //@ close this.x |-> 0;
    }

    
    

    void run()
        //@ requires this.x |-> ?v;
        //@ ensures this.x |-> v + 1;
    {
        //@ open this.x |-> v;
        x++;
        //@ close this.x |-> v + 1;
    }

    int getResult()
        //@ requires this.x |-> ?v;
        //@ ensures this.x |-> v &*& result == v;
    {
        //@ open this.x |-> v;
        int r = x;
        //@ close this.x |-> v;
        return r;
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
        //@ open t.x |-> _;
        int result = t.getResult();
        //@ assert t.x |-> result;
        assert result == 1;
    }

}