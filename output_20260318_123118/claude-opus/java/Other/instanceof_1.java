interface iX {
}

interface iA extends iX {
}

/*@ predicate A_object(A a) = true; @*/

abstract class A implements iA {
  public int intRep(){
    return 10;
  }
  
  public String StringRep(){
    return "A";
  }
}

class B extends A {}

/*@
  predicate B_object(B b) = A_object(b);
@*/

class C extends A {}

/*@
  predicate C_object(C c) = A_object(c);
@*/

class E extends C {}

/*@
  predicate E_object(E e) = C_object(e);
@*/

final class F extends A {}

/*@
  predicate F_object(F f) = A_object(f);
@*/

class main{
  /*@
    requires x != null &*& y != null &*& A_object(x) &*& A_object(y);
    ensures A_object(x) &*& A_object(y);
  @*/
  public static void test(A x, A y)
  {
    A tst = null;
    if (x instanceof C){
      if(x instanceof B){
        /*@ assert false; @*/ 
      }
    }
    if (x instanceof E){
      if (!(x instanceof C)){
        /*@ assert false; @*/ 
      }
      if (!(x instanceof iA)){
        /*@ assert false; @*/ 
      }
    }
    B u = new B();
    if (!(u instanceof iX)){
      /*@ assert false; @*/ 
    }

    if(!(x instanceof iA)){
      /*@ assert false; @*/ 
    }
  }
}