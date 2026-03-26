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
  
  public B()
  //@ requires true;
  //@ ensures B();
  {
    //@ close A();
    //@ close B();
  }
}

class C extends A {
  //@ predicate C() = A();
  
  public C()
  //@ requires true;
  //@ ensures C();
  {
    //@ close A();
    //@ close C();
  }
}

class E extends C {
  //@ predicate E() = C();
  
  public E()
  //@ requires true;
  //@ ensures E();
  {
    //@ close C();
    //@ close E();
  }
}

final class F extends A {
  //@ predicate F() = A();
  
  public F()
  //@ requires true;
  //@ ensures F();
  {
    //@ close A();
    //@ close F();
  }
}

class main{
  public static void test(A x, A y)
  //@ requires x != null &*& y != null &*& x.A() &*& y.A();
  //@ ensures x.A() &*& y.A();
  {
    A tst = null;
    if (x instanceof C){
      //@ open x.A();
      //@ assert x instanceof C;
      //@ close ((C)x).C();
      if(x instanceof B){
        
        //@ assert false;
      }
      //@ close x.A();
    }
    if (x instanceof E){
      //@ open x.A();
      //@ assert x instanceof E;
      //@ close ((E)x).E();
      if (!(x instanceof C)){
        
        //@ assert false;
      }
      if (!(x instanceof iA)){
        
        //@ assert false;
      }
      //@ close x.A();
    }
    B u = new B();
    //@ open u.B();
    //@ open u.A();
    if (!(u instanceof iX)){
       
       //@ assert false;
    }
    //@ close u.A();
    //@ close u.B();
    
    if(!(x instanceof iA)){
      
      //@ open x.A();
      //@ assert false;
    }
  }
}