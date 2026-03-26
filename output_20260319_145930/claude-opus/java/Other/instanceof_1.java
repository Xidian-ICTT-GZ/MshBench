interface iX {
}

interface iA extends iX {
}

abstract class A implements iA {
  public int intRep()
    //@ requires true;
    //@ ensures result == 10;
  {
    return 10;
  }
  
  public String StringRep()
    //@ requires true;
    //@ ensures true;
  {
    return "A";
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
        //@ assert false;
        
      }
    }
    if (x instanceof E){
      if (!(x instanceof C)){
        //@ assert false;
        
      }
      if (!(x instanceof iA)){
        //@ assert false;
        
      }
    }
    B u = new B();
    if (!(u instanceof iX)){
       //@ assert false;
       
    }
    
    if(!(x instanceof iA)){
      //@ assert false;
      
    }
    
    
    

  }
}