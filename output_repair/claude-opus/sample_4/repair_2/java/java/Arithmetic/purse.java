class Purse {
    short balance;
}

class Program {
    Purse p1, p2;

    //@ requires p != null &*& p.Purse_balance |-> ?b;
    //@ ensures p.Purse_balance |-> ?b2;
    void deposit(Purse p, short amount)
    {
        p.balance += amount;
    }

    //@ ensures p1 != null &*& p1.Purse_balance |-> 100 &*& p2 != null &*& p2.Purse_balance |-> 50;
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