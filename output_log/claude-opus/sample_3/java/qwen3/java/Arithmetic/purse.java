class Purse {
    //@ predicate purse(Purse p; short b) = p.balance |-> b;

    short balance;
}

class Program {
    Purse p1, p2;

    //@ requires purse(p; ?b) &*& 0 <= (int)b &*& 0 <= (int)amount &*& (int)b + (int)amount <= Short.MAX_VALUE;
    //@ ensures purse(p; b + amount);
    void deposit(Purse p, short amount)
    //@ terminates
    {
        p.balance += amount;
    }

    //@ requires true;
    //@ ensures p1 != null &*& p2 != null &*& purse(p1; 100) &*& purse(p2; 50);
    Program()
    //@ terminates
    {
        p1 = new Purse();
        //@ close purse(p1; 0);
        deposit(p1, (short) 100);
        //@ open purse(p1; ?b1);
        p2 = new Purse();
        //@ close purse(p2; 0);
        deposit(p2, (short) 50);
        //@ open purse(p2; ?b2);

        short b1 = p1.balance;
        short b2 = p2.balance;
        assert b1 == 100 && b2 == 50;
        //@ close purse(p1; b1);
        //@ close purse(p2; b2);
    }
}