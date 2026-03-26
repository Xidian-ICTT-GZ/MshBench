interface iX {
}

interface iA extends iX {
}

/*@

predicate A_state(A a) = a != null;

@*/

abstract class A implements iA {
  //@ requires A_state(this);
  //@ ensures A_state(this) &*& result == 10;
  public int intRep(){
    return 10;
  }
  
  //@ requires A_state(this);
  //@ ensures A_state(this) &*& result != null;
  public String StringRep(){
    return "A";
  }
}

class B extends A {
  //@ requires true;
  //@ ensures A_state(this);
  public B() {}
}

class C extends A {
  //@ requires true;
  //@ ensures A_state(this);
  public C() {}
}

class E extends C {
  //@ requires true;
  //@ ensures A_state(this);
  public E() {}
}

final class F extends A {
  //@ requires true;
  //@ ensures A_state(this);
  public F() {}
}

class main{
  //@ requires true;
  //@ ensures true;
  public static void test(A x, A y)
    
    
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