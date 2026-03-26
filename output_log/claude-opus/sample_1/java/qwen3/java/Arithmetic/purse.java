class Purse {
  /*@
  predicate purse_inv(Purse p; short b) = p.balance |-> b;
  @*/
  short balance;
}

class Program {
  Purse p1, p2;

  //@ requires purse_inv(p, ?b) &*& 0 <= (int)b + (int)amount &*& (int)b + (int)amount <= Short.MAX_VALUE;
  //@ ensures purse_inv(p, b + amount);
  void deposit(Purse p, short amount)
    //@ requires purse_inv(p, ?b) &*& 0 <= (int)b + (int)amount &*& (int)b + (int)amount <= Short.MAX_VALUE;
    //@ ensures purse_inv(p, b + amount);
  {
    p.balance += amount;
  }

  //@ requires true;
  //@ ensures purse_inv(p1, 100) &*& purse_inv(p2, 50) &*& p1 != null &*& p2 != null;
  Program()
    //@ requires true;
    //@ ensures purse_inv(p1, 100) &*& purse_inv(p2, 50) &*& p1 != null &*& p2 != null;
  {
    p1 = new Purse();
    deposit(p1, (short) 100);
    p2 = new Purse();
    deposit(p2, (short) 50);

    short b1 = p1.balance;
    short b2 = p2.balance;
    assert b1 == 100 && b2 == 50;
  }
}