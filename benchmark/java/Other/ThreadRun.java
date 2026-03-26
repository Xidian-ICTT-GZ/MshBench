

class Thread {

    
    

    Thread()
        
        
    {
    }

    void start()
        
        
    {
        throw new NullPointerException();
    }

    void run()
        
        
    {
        
        
    }

    void join()
        
        
    {
        throw new NullPointerException();
    }

}

class MyThread extends Thread {

    int x;

    MyThread()
        
        
    {
        
    }

    
    

    void run()
        
        
    {
        
        x++;
        
    }

    int getResult()
        
        
    {
        
        return x;
    }
}

class Program {

    public static void main(String[] args)
        
        
    {
        MyThread t = new MyThread();
        t.start();
        t.join();
        int result = t.getResult();
        assert result == 1;
    }

}
