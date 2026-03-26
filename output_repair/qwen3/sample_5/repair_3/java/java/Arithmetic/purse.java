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

    //@ ensures this.p1 |-> ?p1v &*& this.p2 |-> ?p2v &*& p1v != null &*& p2v != null &*& p1v.balance |-> 100 &*& p2v.balance |-> 50;
    Program()
    {
        p1 = new Purse();
        //@ assert this.p1 |-> ?tmp &*& tmp != null &*& tmp.balance |-> 0;
        deposit(p1, (short) 100);
        //@ assert this.p1 |-> ?tmp1 &*& tmp1 != null &*& tmp1.balance |-> 100;
        p2 = new Purse();
        //@ assert this.p2 |-> ?tmp2 &*& tmp2 != null &*& tmp2.balance |-> 0;
        deposit(p2, (short) 50);
        //@ assert this.p2 |-> ?tmp3 &*& tmp3 != null &*& tmp3.balance |-> 50;

        short b1 = p1.balance;
        short b2 = p2.balance;
        assert b1 == 100 && b2 == 50;
    }
}