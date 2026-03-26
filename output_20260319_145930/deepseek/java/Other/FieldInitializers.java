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
  
  //@ predicate A() = this.a |-> 1 &*& this.b |-> 2;
  
  A() 
    //@ requires true;
    //@ ensures A();
  {
    //@ close A();
  }
  
  int getA() 
    //@ requires A();
    //@ ensures A() &*& result == 1;
  {
    //@ open A();
    return this.a;
  }
}

class B extends A {
  //@ predicate B() = A() &*& this.c |-> 1 &*& this.d |-> 11;

  int c = getA(), d = this.c + C.id(10);
  
  B() 
    //@ requires true;
    //@ ensures B();
  {
    super();
    //@ close B();
  }
  
}