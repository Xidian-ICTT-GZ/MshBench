interface iX {
}

interface iA extends iX {
}

abstract class A implements iA {
  //@ public predicate object() = true;
  //@ invariant true;
  
  public int intRep(){
    //@ open object();
    int res = 10;
    //@ close object();
    return res;
  }
  
  public String StringRep(){
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

class main{
  public static void test(A x, A y)
    //@ requires true;
    //@ ensures true;
  {
    A tst = null;
    if (x instanceof C){
      if(x instanceof B){
        //@ // no mutation, just checks
      }
    }
    if (x instanceof E){
      if (!(x instanceof C)){
        //@ // contradiction, no mutation
      }
      if (!(x instanceof iA)){
        //@ // contradiction, no mutation
      }
    }
    B u = new B();
    if (!(u instanceof iX)){
       //@ // u extends A implements iA extends iX always true
    }
    
    if(!(x instanceof iA)){
      //@ // contradiction, as x is A implements iA
    }
  }
}