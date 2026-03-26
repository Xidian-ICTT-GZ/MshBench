class Purse {
    short balance;

    /*@ predicate purse(Purse p; int b) =
          p.balance |-> b &*& 0 <= b &*& b <= 32767;
    @*/
}

class Program {
    Purse p1, p2;

    //@ requires purse(p, ?b) &*& (int)amount >= 0 &*& (int)amount <= 32767 &*& b + (int)amount <= 32767;
    //@ ensures purse(p, b + (int)amount);
    void deposit(Purse p, short amount)
    {
        p.balance += amount;
    }

    //@ requires true;
    //@ ensures purse(p1, 100) &*& purse(p2, 50);
    Program()
    {
        p1 = new Purse();
        deposit(p1, (short)100);
        p2 = new Purse();
        deposit(p2, (short)50);

        short b1 = p1.balance;
        short b2 = p2.balance;
        assert b1 == 100 && b2 == 50;
    }
}