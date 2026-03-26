class Purse {
  /*@ 
    predicate purse(Purse p; int balance) = 
      p.balance |-> balance &*& 0 <= balance &*& balance <= 32767;
  @*/

  short balance;
}

class Program {
  Purse p1, p2;

  /*@ 
    requires purse(p, ?b) &*& 0 <= amount &*& amount <= 32767 &*& b + amount <= 32767;
    ensures purse(p, b + amount);
  @*/
  void deposit(Purse p, short amount)
  {
    //@ open purse(p, ?b);
    p.balance += amount;
    //@ close purse(p, b + amount);
  }

  //@ requires true;
  //@ ensures purse(p1, 100) &*& purse(p2, 50);
  Program()
  {
    p1 = new Purse();
    //@ close purse(p1, 0);
    deposit(p1, (short)100);
    p2 = new Purse();
    //@ close purse(p2, 0);
    deposit(p2, (short)50);

    short b1 = p1.balance;
    short b2 = p2.balance;
    assert b1 == 100 && b2 == 50;
  }
}