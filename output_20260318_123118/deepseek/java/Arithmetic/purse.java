class Purse {
    short balance;
}

class Program {
    Purse p1, p2;

    //@ requires p != null;
    //@ ensures p.balance == \old(p.balance) + amount;
    void deposit(Purse p, short amount)
        
        
    {
        p.balance += amount;
    }

    //@ ensures p1 != null &*& p2 != null;
    //@ ensures p1.balance == 100 &*& p2.balance == 50;
    Program()
        
        
    {
        //@ close PursePred(p1, _);
        p1 = new Purse();
        deposit(p1, (short)100);
        //@ close PursePred(p2, _);
        p2 = new Purse();
        deposit(p2, (short)50);

        short b1 = p1.balance;
        short b2 = p2.balance;
        //@ assert b1 == 100;
        //@ assert b2 == 50;
        assert b1 == 100 && b2 == 50;
    }
}

/*@
predicate PursePred(Purse p; short b) = p != null &*& p.balance |-> b;
@*/