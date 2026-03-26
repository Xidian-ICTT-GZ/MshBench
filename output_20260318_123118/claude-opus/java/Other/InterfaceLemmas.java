interface Counter {
  /*@ 
    predicate counter(int value);

    // get requires ownership of counter predicate
    //@ requires counter(?v);
    //@ ensures counter(v) &*& result == v;

    // set requires ownership of counter predicate
    //@ requires counter(?v);
    //@ ensures counter(value);
  @*/
  public int get();

  public void set(int value);
}

class MyCounter implements Counter {
  int count;

  /*@ predicate counter(int value) = this.count |-> value; @*/

  //@ requires true;
  //@ ensures counter(0); 
  MyCounter() {
  }

  //@ requires counter(?v);
  //@ ensures counter(v) &*& result == v;
  public int get() {
    return count;
  }

  //@ requires counter(?v);
  //@ ensures counter(value);
  public void set(int value) {
    count = value;
  }
}

class Program {
  /*@ 
    // test requires Counter.counter predicate with value >= 0
    //@ requires c.counter(?v) &*& v >= 0;
    //@ ensures c.counter(v);
  @*/
  public static void test(Counter c) {
    int value = c.get();
    //@ open c.counter(?v);
    assert 0 <= value;
    //@ close c.counter(value);
  }

  /*@ 
    //@ requires true;
    //@ ensures true;
  @*/
  public static void main(String[] args) {
    Counter c = new MyCounter();
    //@ close c.counter(0);
    c.set(42);
    //@ open c.counter(?v);
    //@ assert v == 42;
    test(c);
    //@ open c.counter(?v);
  }
}