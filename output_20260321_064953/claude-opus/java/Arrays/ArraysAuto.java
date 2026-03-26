class InitTest {
    /*@
    predicate array_int(int[] xs, int length) = xs != null &*& length == xs.length &*& 0 <= length;
    @*/
    
    static void test2()
        //@ requires true; 
        //@ ensures true;
    {
        int[] xs = new int[100];
        //@ assert xs != null;
        //@ close array_int(xs, 100);
        
        int x = xs[50];
        assert x == 0;
        test3(xs);
    }
    
    static void test3(int[] xs)
        //@ requires true;
        //@ ensures true;
    {
    }
}