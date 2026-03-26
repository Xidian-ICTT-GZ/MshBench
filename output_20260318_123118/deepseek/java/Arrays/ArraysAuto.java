class InitTest {
    //@ predicate array100(int[] a) = a != null &*& a.length == 100 &*& array_slice(a, 0, 100, _);
    //@ predicate array100_perm(int[] a) = a != null &*& a.length == 100 &*& array_slice(a, 0, 100, ?vals) &*& switch(vals) { case cons(h, t): return true; case nil: return false; };

    static void test2()
        //@ requires true;
        //@ ensures true;
    {
        int[] xs = new int[100];
        //@ close array100(xs);
        //@ close array100_perm(xs);
        
        //@ open array100_perm(xs);
        //@ open array100(xs);
        int x = xs[50];
        //@ close array100(xs);
        assert x == 0;
        test3(xs);
    }
    
    static void test3(int[] xs)
        //@ requires array100(xs);
        //@ ensures array100(xs);
    {
        //@ open array100(xs);
        //@ close array100(xs);
    }
}