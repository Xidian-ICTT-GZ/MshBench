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
    
    //@ requires array_slice(xs, 0, length(xs), _);
    //@ ensures array_slice(xs, 0, length(xs), _);
    static void test3(int[] xs)
        
        
    {
    }
    
    /*@
    predicate array_slice(int[] a, int from, int count, list<int> elems) =
        from >= 0 &*& count >= 0 &*& from + count <= length(a) &*&
        a != null &*&
        array_slice_elems(a, from, count, elems);
    @*/
    
    /*@
    fixpoint list<int> array_slice_elems(int[] a, int from, int count) {
        return count == 0 ? nil : cons(a[from], array_slice_elems(a, from + 1, count - 1));
    }
    @*/
}