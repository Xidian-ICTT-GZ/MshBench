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
        //@ ensures true;
    {
        
    }

    
    

    void run()
        //@ requires true;
        //@ ensures true;
    {
        
        x++;
        
    }

    int getResult()
        //@ requires true;
        //@ ensures true;
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
        //@ assert result == 1;
    }

}