class Purse {
    short balance;
}

class Program {
    Purse p1, p2;

    //@ requires p != null &*& p.balance |-> ?b &*& b + amount <= 32767 &*& -32768 <= b + amount;
    //@ ensures p.balance |-> (b + amount);
    void deposit(Purse p, short amount)
    {
        p.balance += amount;
    }

    //@ ensures this.p1 |-> ?p1v &*& p1v != null &*& p1v.balance |-> 100 &*& this.p2 |-> ?p2v &*& p2v != null &*& p2v.balance |-> 50;
    Program()
    {
        p1 = new Purse();
        //@ assert p1.balance |-> 0;
        deposit(p1, (short) 100);
        //@ assert p1.balance |-> 100;
        p2 = new Purse();
        //@ assert p2.balance |-> 0;
        deposit(p2, (short) 50);
        //@ assert p2.balance |-> 50;

        short b1 = p1.balance;
        short b2 = p2.balance;
        assert b1 == 100 && b2 == 50;
    }
}