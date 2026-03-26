interface iX {
}

interface iA extends iX {
}

abstract class A implements iA {
  /*@
  predicate object();
  @*/

  public int intRep()
    //@ requires object();
    //@ ensures object() &*& result == 10;
  {
    //@ open object();
    int res = 10;
    //@ close object();
    return res;
  }
  
  public String StringRep()
    //@ requires object();
    //@ ensures object() &*& result != null;
  {
    //@ open object();
    String res = "A";
    //@ close object();
    return res;
  }
}

class B extends A {}

class C extends A {}

class E extends C {}

final class F extends A {}

class main {
  public static void test(A x, A y)
    //@ requires true;
    //@ ensures true;
  {
    A tst = null;
    if (x instanceof C) {
      if (x instanceof B) {
        //@ // no mutation or ownership assumptions
      }
    }
    if (x instanceof E) {
      if (!(x instanceof C)) {
        //@ // contradicts subclassing: no code
      }
      if (!(x instanceof iA)) {
        //@ // contradicts interface: no code
      }
    }
    B u = new B();
    if (!(u instanceof iX)) {
      //@ // impossible, u implements iA extends iX
    }
    if (!(x instanceof iA)) {
      //@ // x is A implements iA, so impossible
    }
  }
}