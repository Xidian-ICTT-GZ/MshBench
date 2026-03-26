class InitTest {
    /*@
    predicate array_int(int[] arr, int length) = true;
    @*/

    static void test2()
    //@ requires true;
    //@ ensures true;
    {
        int[] xs = new int[100];
        //@ close array_int(xs, 100);
        int x = xs[50];
        assert x == 0;
        test3(xs);
    }
    
    static void test3(int[] xs)
    //@ requires array_int(xs, ?length);
    //@ ensures array_int(xs, length);
    {
    }
}