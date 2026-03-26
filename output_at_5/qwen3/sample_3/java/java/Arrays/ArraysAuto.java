class InitTest {
    /*@
    predicate array(int[] xs) = true;
    @*/

    static void test2()
        //@ requires true;
        //@ ensures true;
        
    {
        int[] xs = new int[100];
        /*@ open array(xs); @*/
        
        int x = xs[50];
        assert x == 0;
        test3(xs);
        /*@ close array(xs); @*/
    }
    
    static void test3(int[] xs)
        //@ requires array(xs);
        //@ ensures true;
        
        
    {
    }
}