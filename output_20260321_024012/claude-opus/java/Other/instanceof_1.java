interface iX {
}

interface iA extends iX {
}

abstract class A implements iA {
  //@ public invariant true;
  public int intRep(){
    //@ requires true;
    //@ ensures true;
    return 10;
  }
  
  public String StringRep(){
    //@ requires true;
    //@ ensures true;
    return "A";
  }
}

class B extends A {}

class C extends A {}

class E extends C {}

final class F extends A {}

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