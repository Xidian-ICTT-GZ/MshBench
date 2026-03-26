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
    //@ ensures this.a &*& this.b;
  {
   
  }
  
  int getA() 
    //@ requires this.a &*& this.b;
    //@ ensures result == this.a &*& this.a &*& this.b;
  {
    return this.a;
  }
}

class B extends A {

  int c = getA(), d = this.c + C.id(10);
  
  B() 
    //@ requires true;
    //@ ensures this.a &*& this.b &*& this.c &*& this.d;
  {
    super();
  }
  
}