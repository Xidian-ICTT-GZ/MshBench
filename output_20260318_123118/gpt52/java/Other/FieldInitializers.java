class C {
  static int id(int x)
  //@ requires true;
  //@ ensures result == x;
  {
    return x;
  }
}

class A {
  int a = 1, b = 2;
  
  /*@ predicate a_state() =
        this.a |-> 1
    &*& this.b |-> 2;
  @*/
  
  A() 
  //@ requires true;
  //@ ensures a_state();
  {
   
  }
  
  int getA() 
  //@ requires this.a |-> ?v;
  //@ ensures this.a |-> v &*& result == v;
  {
    return this.a;
  }
}

class B extends A {

  int c = getA(), d = this.c + C.id(10);
  
  /*@ predicate b_state() =
        a_state()
    &*& this.c |-> 1
    &*& this.d |-> 11;
  @*/
  
  B() 
  //@ requires true;
  //@ ensures b_state();
  {
    super();
  }
  
}