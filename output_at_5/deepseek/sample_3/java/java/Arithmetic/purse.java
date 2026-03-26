class Purse {
    short balance;
    
    //@ predicate Purse() = balance |-> _;
    
    Purse()
    //@ requires true;
    //@ ensures Purse();
    {
        //@ close Purse();
    }
}

class Program {
    Purse p1, p2;
    
    //@ predicate Program() = p1 |-> ?p1v &*& p2 |-> ?p2v &*& (p1v != null ? p1v.Purse() : true) &*& (p2v != null ? p2v.Purse() : true);

    void deposit(Purse p, short amount)
    //@ requires p.Purse();
    //@ ensures p.Purse();
    {
        //@ open p.Purse();
        p.balance += amount;
        //@ close p.Purse();
    }

    Program()
    //@ requires true;
    //@ ensures Program();
    {
        //@ close Program();
        p1 = new Purse();
        deposit(p1, (short)100);
        p2 = new Purse();
        deposit(p2, (short)50);
        //@ open p1.Purse();
        //@ open p2.Purse();
        short b1 = p1.balance;
        short b2 = p2.balance;
        //@ close p1.Purse();
        //@ close p2.Purse();
        assert b1 == 100 && b2 == 50;
    }
}