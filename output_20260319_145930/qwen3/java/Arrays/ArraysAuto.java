class InitTest {
    //@ requires true;
    //@ ensures true;
    static void test2()
        
        
    {
        int[] xs = new int[100];
        //@ close array_slice(xs, 0, 100, _);
        
        int x = xs[50];
        //@ open array_slice(xs, 0, 100, _);
        assert x == 0;
        //@ close array_slice(xs, 0, 100, _);
        test3(xs);
    }
    
    //@ requires array_slice(xs, 0, xs.length, _);
    //@ ensures true;
    static void test3(int[] xs)
        
        
    {
        //@ open array_slice(xs, 0, xs.length, _);
    }
}