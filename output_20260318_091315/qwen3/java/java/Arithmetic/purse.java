/*@ predicate purse(Purse p; short v) = p.balance |-> v; @*/

class Purse {
    short balance;
}

class Program {
    Purse p1, p2;

    //@ requires purse(p, ?v) &*& amount >= 0 &*& v >= 0 &*& (short)(v + amount) == v + amount;
    //@ ensures purse(p, v + amount);
    void deposit(Purse p, short amount)
    {
        p.balance += amount;
    }

    //@ requires true;
    //@ ensures true;
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