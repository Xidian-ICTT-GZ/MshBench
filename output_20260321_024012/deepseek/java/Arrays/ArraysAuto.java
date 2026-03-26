class InitTest {
    //@ requires true;
    //@ ensures true;
    static void test2()
        
        
    {
        //@ close array_slice(xs, 0, 100, _);
        int[] xs = new int[100];
        //@ open array_slice(xs, 0, 100, _);
        
        //@ assert array_slice(xs, 50, 1, _);
        //@ open array_slice(xs, 50, 1, _);
        int x = xs[50];
        //@ close array_slice(xs, 50, 1, _);
        assert x == 0;
        //@ close array_slice(xs, 0, 100, _);
        test3(xs);
    }
    
    //@ requires array_slice(xs, 0, 100, _);
    //@ ensures array_slice(xs, 0, 100, _);
    static void test3(int[] xs)
        
        
    {
    }
    
    /*@
    predicate array_slice(int[] a, int from, int to, list<int> contents) =
        from <= to &*& to <= a.length &*& a != null &*& ints(a, from, to, contents);
    @*/
}