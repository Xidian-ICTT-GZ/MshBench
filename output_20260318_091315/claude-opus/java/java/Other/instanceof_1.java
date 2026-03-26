interface iX {
}

interface iA extends iX {
}

abstract class A implements iA {
  //@ predicate valid() = this instanceof A;
  //@ ensures result == 10 &*& valid();
  public int intRep(){
    return 10;
  }
  
  //@ predicate stringRepValid() = this instanceof A;
  //@ ensures result != null &*& stringRepValid();
  public String StringRep(){
    return "A";
  }
}

class B extends A {}

class C extends A {}

class E extends C {}

final class F extends A {}

class main{
  /*@ 
    @ requires x != null &*& y != null &*& x instanceof A &*& y instanceof A;
    @ ensures true;
    @*/
  public static void test(A x, A y)
  {
    A tst = null;
    if (x instanceof C){
      if(x instanceof B){
        //@ assert x instanceof C &*& x instanceof B;
      }
    }
    if (x instanceof E){
      if (!(x instanceof C)){
        //@ assert false; // E extends C so this should be impossible
      }
      if (!(x instanceof iA)){
        //@ assert false; // E extends C extends A implements iA, impossible
      }
    }
    B u = new B();
    if (!(u instanceof iX)){
      //@ assert false; // B extends A implements iA extends iX
    }
    
    if(!(x instanceof iA)){
      //@ assert false; // x instanceof A implies x instanceof iA
    }
  }
}