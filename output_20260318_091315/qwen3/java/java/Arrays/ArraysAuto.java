/*@ predicate array_slice(int[] a, int start, int len; int v) =
    start >= 0 &*& len >= 0 &*&
    chars((char*)a + sizeof(int) * start, len * sizeof(int)) |-> ?cs &*&
    cs == repeat(len, (char)v);
@*/

class InitTest {
    //@ requires true;
    //@ ensures true;
    static void test2() {
        int[] xs = new int[100];
        //@ assert array_slice(xs, 0, 100, 0);
        
        int x = xs[50];
        //@ assert x == 0;
        assert x == 0;
        test3(xs);
    }
    
    //@ requires array_slice(xs, 0, 100, 0);
    //@ ensures true;
    static void test3(int[] xs) {
    }
}