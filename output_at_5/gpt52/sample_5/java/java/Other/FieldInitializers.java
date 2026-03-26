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
  
  /*@
  predicate A_inv(A this; int va, int vb) = this.a |-> va &*& this.b |-> vb;
  @*/
  
  A() 
   
   
  //@ requires true;
  //@ ensures A_inv(this, 1, 2);
  {
   //@ close A_inv(this, 1, 2);
  }
  
  int getA() 
    
    
  //@ requires A_inv(this, ?va, ?vb);
  //@ ensures A_inv(this, va, vb) &*& result == va;
  {
    //@ open A_inv(this, va, vb);
    int r = this.a;
    //@ close A_inv(this, va, vb);
    return r;
  }
}

class B extends A {

  int c = getA(), d = this.c + C.id(10);
  
  /*@
  predicate B_inv(B this; int va, int vb, int vc, int vd) = A_inv(this, va, vb) &*& this.c |-> vc &*& this.d |-> vd;
  @*/
  
  B() 
    
    
  //@ requires true;
  //@ ensures B_inv(this, 1, 2, 1, 11);
  {
    super();
    //@ close A_inv(this, 1, 2);
    //@ close B_inv(this, 1, 2, 1, 11);
  }
  
}