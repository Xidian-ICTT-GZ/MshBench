interface iX {
}

interface iA extends iX {
}

abstract class A implements iA {
  //@ predicate A() = true;
  
  public int intRep()
  //@ requires A();
  //@ ensures A() &*& result == 10;
  {
    return 10;
  }
  
  public String StringRep()
  //@ requires A();
  //@ ensures A() &*& result != null;
  {
    return "A";
  }
}

class B extends A {
  //@ predicate B() = A();
}

class C extends A {
  //@ predicate C() = A();
}

class E extends C {
  //@ predicate E() = C();
}

final class F extends A {
  //@ predicate F() = A();
}

class main{
  public static void test(A x, A y)
  //@ requires x != null &*& y != null &*& x.A() &*& y.A();
  //@ ensures x.A() &*& y.A();
  {
    A tst = null;
    if (x instanceof C){
      //@ open x.A();
      //@ close ((C)x).C();
      if(x instanceof B){
        //@ open ((C)x).C();
        //@ close ((B)x).B();
      }
      //@ close x.A();
    }
    if (x instanceof E){
      //@ open x.A();
      //@ close ((E)x).E();
      if (!(x instanceof C)){
        
      }
      if (!(x instanceof iA)){
        
      }
      //@ close x.A();
    }
    B u = new B();
    //@ close u.B();
    if (!(u instanceof iX)){
       
    }
    
    if(!(x instanceof iA)){
      
    }
  }
}