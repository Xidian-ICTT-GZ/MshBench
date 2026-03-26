class Purse {
    short balance;

    /*@
    predicate purse(short b) =
        balance |-> b;
    @*/
}

class Program {
    Purse p1, p2;

    //@ requires p != null &*& p.purse(?b);
    //@ ensures p.purse(b + amount);
    void deposit(Purse p, short amount)
        
        
    {
        //@ open p.purse(_);
        p.balance += amount;
        //@ close p.purse(p.balance);
    }

    //@ ensures true;
    Program()
        
        
    {
        p1 = new Purse();
        //@ close p1.purse((short)0);
        deposit(p1, (short)100);
        p2 = new Purse();
        //@ close p2.purse((short)0);
        deposit(p2, (short)50);

        short b1 = p1.balance;
        short b2 = p2.balance;
        //@ open p1.purse(_);
        //@ open p2.purse(_);
        assert b1 == 100 && b2 == 50;
    }
}