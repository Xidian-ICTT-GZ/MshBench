class Purse {
    short balance;
    
    //@ predicate Purse() = balance |-> _;
    
    //@ requires true;
    //@ ensures Purse();
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

    //@ requires p != null &*& p.Purse();
    //@ ensures p.Purse();
    void deposit(Purse p, short amount)
        //@ requires p != null &*& p.Purse();
        //@ ensures p.Purse();
    {
        //@ open p.Purse();
        p.balance += amount;
        //@ close p.Purse();
    }

    //@ requires true;
    //@ ensures Program();
    Program()
        //@ requires true;
        //@ ensures Program();
    {
        //@ close Program();
        //@ open Program();
        p1 = new Purse();
        //@ open p1.Purse();
        //@ close p1.Purse();
        deposit(p1, (short)100);
        p2 = new Purse();
        //@ open p2.Purse();
        //@ close p2.Purse();
        deposit(p2, (short)50);

        //@ open p1.Purse();
        short b1 = p1.balance;
        //@ close p1.Purse();
        //@ open p2.Purse();
        short b2 = p2.balance;
        //@ close p2.Purse();
        assert b1 == 100 && b2 == 50;
        //@ close Program();
    }
}