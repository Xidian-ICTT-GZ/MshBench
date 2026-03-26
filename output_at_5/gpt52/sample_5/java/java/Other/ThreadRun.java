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
        //@ requires MyThread_inv();
        //@ ensures MyThread_inv();
        
        
    {
        //@ open MyThread_inv();
        x++;
        //@ close MyThread_inv();
        
    }

    int getResult()
        //@ requires MyThread_inv();
        //@ ensures MyThread_inv();
        
        
    {
        //@ open MyThread_inv();
        
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