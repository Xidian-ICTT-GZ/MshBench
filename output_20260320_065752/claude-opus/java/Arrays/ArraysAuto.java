class InitTest {
    /*@
    predicate array_int(int[] a, int length) = a != null &*& a.length == length &*& a |-> ?contents &*& array_elements(a, 0, length, contents);
    
    fixpoint bool array_elements(int[] a, int from, int to, list<int> contents) {
        return from == to ? true :
            a[from] |-> ?v &*& array_elements(a, from + 1, to, tail(contents));
    }
    @*/

    static void test2()
    //@ requires true;
    //@ ensures true;
    {
        int[] xs = new int[100];
        //@ assume xs != null;
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