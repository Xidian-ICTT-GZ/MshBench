class InitTest {
    //@ requires true;
    //@ ensures true;
    static void test2()
        
        
    {
        int[] xs = new int[100];
        
        int x = xs[50];
        assert x == 0;
        test3(xs);
    }
    
    //@ requires true;
    //@ ensures true;
    static void test3(int[] xs)
        
        
    {
    }
}