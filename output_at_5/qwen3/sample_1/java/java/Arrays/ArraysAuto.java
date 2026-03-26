class InitTest {
    /*@
    predicate array(int[] xs, int length) = xs != null &*& 0 <= length;
    @*/

    static void test2()
        //@ requires true;
        //@ ensures true;
        
    {
        int[] xs = new int[100];
        /*@ open array(xs, 100); @*/
        
        int x = xs[50];
        assert x == 0;
        test3(xs);
        /*@ close array(xs, 100); @*/
    }
    
    static void test3(int[] xs)
        //@ requires array(xs, _);
        //@ ensures true;
        
        
    {
    }
}