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
  
  public int intRep()
  //@ requires B();
  //@ ensures B() &*& result == 10;
  {
    return 10;
  }
  
  public String StringRep()
  //@ requires B();
  //@ ensures B() &*& result != null;
  {
    return "A";
  }
}

class C extends A {
  //@ predicate C() = A();
  
  public int intRep()
  //@ requires C();
  //@ ensures C() &*& result == 10;
  {
    return 10;
  }
  
  public String StringRep()
  //@ requires C();
  //@ ensures C() &*& result != null;
  {
    return "A";
  }
}

class E extends C {
  //@ predicate E() = C();
  
  public int intRep()
  //@ requires E();
  //@ ensures E() &*& result == 10;
  {
    return 10;
  }
  
  public String StringRep()
  //@ requires E();
  //@ ensures E() &*& result != null;
  {
    return "A";
  }
}

final class F extends A {
  //@ predicate F() = A();
  
  public int intRep()
  //@ requires F();
  //@ ensures F() &*& result == 10;
  {
    return 10;
  }
  
  public String StringRep()
  //@ requires F();
  //@ ensures F() &*& result != null;
  {
    return "A";
  }
}

class main{
  public static void test(A x, A y)
  //@ requires x != null &*& y != null;
  //@ ensures true;
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
    if (!(u instanceof iX)){
       
       
    }
    
    if(!(x instanceof iA)){
      
      
    }
    
    
    

  }
}