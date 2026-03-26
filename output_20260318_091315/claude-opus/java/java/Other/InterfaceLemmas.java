interface Counter {
  /*@ 
    predicate counter(int value);

    //@ requires counter(?v);
    //@ ensures counter(v) &*& result == v;
    public int get();

    //@ requires counter(?v);
    //@ ensures counter(value);
    public void set(int value);
  @*/
}

class MyCounter implements Counter {
  int count;

  /*@ 
    predicate counter(int value) = this.count |-> value;
  @*/

  /*@ 
    //@ requires true;
    //@ ensures counter(0);
  @*/
  MyCounter() {
  }

  /*@ 
    //@ requires counter(?v);
    //@ ensures counter(v) &*& result == v;
  @*/
  public int get() {
    return count;
  }

  /*@ 
    //@ requires counter(?v);
    //@ ensures counter(value);
  @*/
  public void set(int value) {
    count = value;
  }
}

class Program {
  /*@ 
    //@ requires c.counter(?v);
    //@ ensures c.counter(v);
  @*/
  public static void test(Counter c) {
    int value = c.get();
    //@ open c.counter(value);
    assert 0 <= value;
    //@ close c.counter(value);
  }

  /*@ 
    //@ requires true;
    //@ ensures true;
  @*/
  public static void main(String[] args) {
    Counter c = new MyCounter();
    c.set(42);
    test(c);
  }
}