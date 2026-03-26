interface iX {
}

interface iA extends iX {
}

abstract class A implements iA {
  //@ predicate valid() = true;
  public int intRep()
  //@ requires valid();
  //@ ensures valid() &*& result == 10;
  {
    return 10;
  }
  
  public String StringRep()
  //@ requires valid();
  //@ ensures valid() &*& result != null;
  {
    return "A";
  }
}

class B extends A {
  //@ predicate valid() = true;
}

class C extends A {
  //@ predicate valid() = true;
}

class E extends C {
  //@ predicate valid() = true;
}

final class F extends A {
  //@ predicate valid() = true;
}

class main{
  public static void test(A x, A y)
  //@ requires x != null &*& y != null &*& x.valid() &*& y.valid();
  //@ ensures x.valid() &*& y.valid();
  {
    A tst = null;
    if (x instanceof C){
      if(x instanceof B){
      }
    }
    if (x instanceof E){
      if (!(x instanceof C)){
      }
      if (!(x instanceof iA)){
      }
    }
    B u = new B();
    //@ close u.valid();
    if (!(u instanceof iX)){
    }
    
    if(!(x instanceof iA)){
    }
  }
}