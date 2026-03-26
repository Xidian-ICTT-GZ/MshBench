class C {
  static int id(int x)
  //@ requires true;
  //@ ensures result == x;
  {
    return x;
  }
}

/*@

predicate A_inv(A o) =
  o.a |-> ?av &*& o.b |-> ?bv;

predicate B_inv(B o) =
  A_inv(o) &*& o.c |-> ?cv &*& o.d |-> ?dv;

@*/

class A {
  int a = 1, b = 2;
  
  A() 
  //@ requires true;
  //@ ensures A_inv(this);
  {
    //@ close A_inv(this);
  }
  
  int getA() 
  //@ requires A_inv(this);
  //@ ensures A_inv(this) &*& result == this.a;
  {
    //@ open A_inv(this);
    int res = this.a;
    //@ close A_inv(this);
    return res;
  }
}

class B extends A {

  int c = getA(), d = this.c + C.id(10);
  
  B() 
  //@ requires true;
  //@ ensures B_inv(this);
  {
    //@ close A_inv(this);
    super();
    //@ open A_inv(this);
    //@ close A_inv(this);
    //@ close B_inv(this);
  }
  
}