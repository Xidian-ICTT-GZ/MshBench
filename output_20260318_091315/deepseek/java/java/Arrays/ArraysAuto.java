class InitTest {
    //@ predicate array100(int[] a) = a != null &*& a.length == 100 &*& array_slice(a, 0, 100, _);
    //@ predicate array100_perm(int[] a) = a != null &*& a.length == 100 &*& array_slice_perm(a, 0, 100, _);

    //@ requires true;
    //@ ensures true;
    static void test2()
        
        
    {
        int[] xs = new int[100];
        //@ close array100_perm(xs);
        //@ close array100(xs);
        
        int x = xs[50];
        //@ open array100(xs);
        //@ open array100_perm(xs);
        assert x == 0;
        test3(xs);
    }
    
    //@ requires array100(xs);
    //@ ensures array100(xs);
    static void test3(int[] xs)
        
        
    {
    }
}