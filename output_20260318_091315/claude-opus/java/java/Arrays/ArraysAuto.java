class InitTest {
  /*@ predicate ints(int[] a, int i, int n) =
        i == n ?
          true
        :
          0 <= i &*& i < n &*& a[i] |-> ?v &*& ints(a, i + 1, n); @*/

  static void test2()
    //@ requires true;
    //@ ensures true;
  {
    int[] xs = new int[100];
    //@ open ints(xs, 0, 0);
    //@ close ints(xs, 0, 100);
    int x = xs[50];
    assert x == 0;
    test3(xs);
  }

  static void test3(int[] xs)
    //@ requires ints(xs, 0, 100);
    //@ ensures ints(xs, 0, 100);
  {
  }
}