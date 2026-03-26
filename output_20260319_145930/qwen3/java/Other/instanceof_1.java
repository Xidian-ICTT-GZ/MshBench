/*@ predicate iX_pred(iX x;) = true; @*/
/*@ predicate iA_pred(iA a;) = iX_pred(a); @*/
/*@ predicate A_pred(A a;) = iA_pred(a); @*/
/*@ predicate B_pred(B b;) = A_pred(b); @*/
/*@ predicate C_pred(C c;) = A_pred(c); @*/
/*@ predicate E_pred(E e;) = C_pred(e); @*/
/*@ predicate F_pred(F f;) = A_pred(f); @*/

interface iX {
}

interface iA extends iX {
}

abstract class A implements iA {
  //@ requires true;
  //@ ensures result == 10;
  public int intRep(){
    return 10;
  }
  
  //@ requires true;
  //@ ensures result.equals("A");
  public String StringRep(){
    return "A";
  }
}

class B extends A {
  //@ requires true;
  //@ ensures B_pred(this);
  public B() {
    //@ close B_pred(this);
  }
}

class C extends A {
  //@ requires true;
  //@ ensures C_pred(this);
  public C() {
    //@ close C_pred(this);
  }
}

class E extends C {
  //@ requires true;
  //@ ensures E_pred(this);
  public E() {
    //@ close E_pred(this);
  }
}

final class F extends A {
  //@ requires true;
  //@ ensures F_pred(this);
  public F() {
    //@ close F_pred(this);
  }
}

class main{
  //@ requires A_pred(x) &*& A_pred(y);
  //@ ensures true;
  public static void test(A x, A y)
  {
    A tst = null;
    if (x instanceof C){
      //@ open C_pred((C)x);
      //@ close C_pred((C)x);
      if(x instanceof B){
        //@ open B_pred((B)x);
        //@ close B_pred((B)x);
      }
    }
    if (x instanceof E){
      //@ open E_pred((E)x);
      //@ close E_pred((E)x);
      if (!(x instanceof C)){
        //@ assert false;
      }
      if (!(x instanceof iA)){
        //@ assert false;
      }
    }
    B u = new B();
    //@ open B_pred(u);
    //@ close B_pred(u);
    if (!(u instanceof iX)){
      //@ assert false;
    }
    
    if(!(x instanceof iA)){
      //@ assert false;
    }
  }
}