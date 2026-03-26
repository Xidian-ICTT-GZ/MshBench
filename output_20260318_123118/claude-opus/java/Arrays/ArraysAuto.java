class InitTest {
  /*@ predicate array_int(int[] xs, int i, int length) =
        i == length ?
          emp
        :
          xs[i] |-> _ &*& array_int(xs, i + 1, length);
  @*/

  //@ requires true;
  //@ ensures true;
  static void test2()
  {
    int[] xs = new int[100];
    //@ close array_int(xs, 0, 100);
    int x = xs[50];
    //@ open array_int(xs, 0, 100);
    //@ assert xs[50] |-> x;
    //@ close array_int(xs, 0, 100);

    assert x == 0;
    test3(xs);
  }

  //@ requires array_int(xs, 0, xs.length);
  //@ ensures array_int(xs, 0, xs.length);
  static void test3(int[] xs)
  {
  }
}