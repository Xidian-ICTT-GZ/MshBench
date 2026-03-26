class Purse {
    short balance;
    
    //@ predicate Purse(short b) = balance |-> b;
    
    Purse()
    //@ requires true;
    //@ ensures Purse((short)0);
    {
        //@ close Purse((short)0);
    }
}

class Program {
    Purse p1, p2;
    
    //@ predicate Program() = p1 |-> ?p1v &*& p2 |-> ?p2v &*& (p1v != null ? p1v.Purse(_) : true) &*& (p2v != null ? p2v.Purse(_) : true);

    void deposit(Purse p, short amount)
    //@ requires p.Purse(?old) &*& 0 <= amount && amount <= 32767 - old;
    //@ ensures p.Purse((short)(old + amount));
    {
        //@ open p.Purse(old);
        p.balance += amount;
        //@ close p.Purse((short)(old + amount));
    }

    Program()
    //@ requires true;
    //@ ensures Program();
    {
        //@ close Program();
        p1 = new Purse();
        //@ open p1.Purse(_);
        //@ close p1.Purse((short)0);
        deposit(p1, (short)100);
        p2 = new Purse();
        //@ open p2.Purse(_);
        //@ close p2.Purse((short)0);
        deposit(p2, (short)50);
        //@ open p1.Purse(_);
        //@ open p2.Purse(_);
        short b1 = p1.balance;
        short b2 = p2.balance;
        //@ close p1.Purse(b1);
        //@ close p2.Purse(b2);
        assert b1 == 100 && b2 == 50;
    }
}