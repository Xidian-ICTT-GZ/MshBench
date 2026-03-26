class Purse {
    /*@ predicate purse(Purse p; short b) = p.balance |-> b; @*/
    short balance;
}

class Program {
    Purse p1, p2;

    //@ requires purse(p, ?b);
    //@ ensures purse(p, b + amount);
    void deposit(Purse p, short amount)
    //@ requires purse(p, ?b);
    //@ ensures purse(p, b + amount);
    {
        p.balance += amount;
    }

    //@ requires true;
    //@ ensures p1 != null &*& purse(p1, 100) &*& p2 != null &*& purse(p2, 50);
    Program()
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