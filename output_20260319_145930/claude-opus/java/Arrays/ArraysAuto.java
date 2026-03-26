class InitTest {
    static void test2()
        //@ requires true;
        //@ ensures true;
    {
        int[] xs = new int[100];
        
        int x = xs[50];
        assert x == 0;
        test3(xs);
    }
    
    static void test3(int[] xs)
        //@ requires xs != null &*& array_slice(xs, 0, xs.length, _);
        //@ ensures array_slice(xs, 0, xs.length, _);
    {
    }
}