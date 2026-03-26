/*@ 
predicate thread_MyThread(MyThread t; int x) = t.x |-> x;
@*/

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
        //@ close thread_MyThread(this, 0);
    }

    
    

    void run()
        
        
    {
        //@ open thread_MyThread(this, _);
        x++;
        //@ close thread_MyThread(this, x);
    }

    int getResult()
        
        
    {
        //@ open thread_MyThread(this, _);
        int tmp = x;
        //@ close thread_MyThread(this, tmp);
        return tmp;
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