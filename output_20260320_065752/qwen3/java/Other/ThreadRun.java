class Thread {

    //@ predicate thread_pred() = true;

    Thread()
        
        
    {
        //@ close thread_pred();
    }

    void start()
        
        
    {
        //@ open thread_pred();
        throw new NullPointerException();
    }

    void run()
        
        
    {
        
        
    }

    void join()
        
        
    {
        //@ open thread_pred();
        throw new NullPointerException();
    }

}

class MyThread extends Thread {

    int x;

    //@ predicate mythread_pred() = x |-> ?v &*& thread_pred();

    MyThread()
        
        
    {
        //@ close mythread_pred();
    }

    
    

    void run()
        
        
    {
        //@ open mythread_pred();
        x++;
        //@ close mythread_pred();
        
    }

    int getResult()
        
        
    {
        //@ open mythread_pred();
        int tmp = x;
        //@ close mythread_pred();
        return tmp;
    }
}

class Program {

    public static void main(String[] args)
        
        
    {
        MyThread t = new MyThread();
        //@ open t.mythread_pred();
        t.start();
        t.join();
        int result = t.getResult();
        assert result == 1;
    }

}