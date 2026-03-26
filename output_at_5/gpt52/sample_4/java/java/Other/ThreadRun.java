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

    /*@
    predicate MyThread_inv() = this.x |-> _;
    @*/

    MyThread()
        //@ requires true;
        //@ ensures MyThread_inv();
        
        
    {
        //@ close MyThread_inv();
        
    }

    
    

    void run()
        //@ requires true;
        //@ ensures true;
        
        
    {
        
        x++;
        
    }

    int getResult()
        //@ requires MyThread_inv();
        //@ ensures MyThread_inv();
        
        
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
        t.start();
        t.join();
        //@ open t.MyThread_inv();
        //@ close t.MyThread_inv();
        int result = t.getResult();
        assert result == 1;
    }

}