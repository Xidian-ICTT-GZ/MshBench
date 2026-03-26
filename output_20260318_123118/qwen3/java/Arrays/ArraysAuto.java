/*@ predicate array_slice(int[] a, int start, int end; int v) =
    start <= end &*&
    chars(a, start * sizeof(int), (end - start) * sizeof(int)) |-> ?cs &*&
    cs == repeat((end - start), v); @*/

class InitTest {
    //@ requires true;
    //@ ensures true;
    static void test2()
        
        
    {
        int[] xs = new int[100];
        //@ assert chars(xs, 0, 400) |-> ?cs &*& cs == repeat(100, 0);
        
        int x = xs[50];
        assert x == 0;
        test3(xs);
    }
    
    //@ requires chars(xs, 0, ?n) |-> ?cs &*& n >= 0;
    //@ ensures chars(xs, 0, n) |-> cs;
    static void test3(int[] xs)
        
        
    {
    }
}