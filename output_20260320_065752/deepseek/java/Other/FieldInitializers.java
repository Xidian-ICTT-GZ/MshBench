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
  
  A() 
  //@ requires true;
  //@ ensures true;
  {
   
  }
  
  int getA() 
  //@ requires true;
  //@ ensures result == this.a;
  {
    return this.a;
  }
}

class B extends A {

  int c = getA(), d = this.c + C.id(10);
  
  B() 
  //@ requires true;
  //@ ensures true;
  {
    super();
  }
  
}