class Purse {
    short balance;
}

class Program {
    Purse p1, p2;

    //@ requires p != null &*& p.balance |-> ?v;
    //@ ensures p.balance |-> (short)(v + amount);
    void deposit(Purse p, short amount)
        
        
    {
        p.balance += amount;
    }

    //@ ensures p1 != null &*& p1.balance |-> 100 &*& p2 != null &*& p2.balance |-> 50;
    Program()
        
        
    {
        p1 = new Purse();
        //@ close purse(p1);
        deposit(p1, (short)100);
        p2 = new Purse();
        //@ close purse(p2);
        deposit(p2, (short)50);

        short b1 = p1.balance;
        short b2 = p2.balance;
        assert b1 == 100 && b2 == 50;
    }

    //@ predicate purse(Purse p) = p.balance |-> _;
}