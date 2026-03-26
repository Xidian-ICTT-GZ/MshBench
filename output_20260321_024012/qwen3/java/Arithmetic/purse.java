class Purse {
    short balance;
}

/*@
predicate purse(Purse p; short bal) = p.balance |-> bal;
@*/

class Program {
    Purse p1, p2;

    //@ requires purse(p, ?oldBal);
    //@ ensures purse(p, oldBal + amount);
    void deposit(Purse p, short amount)
        
        
    {
        //@ open purse(p, _);
        p.balance += amount;
        //@ close purse(p, p.balance);
    }

    //@ requires true;
    //@ ensures true;
    Program()
        
        
    {
        p1 = new Purse();
        //@ close purse(p1, (short)0);
        deposit(p1, (short)100);
        p2 = new Purse();
        //@ close purse(p2, (short)0);
        deposit(p2, (short)50);

        //@ open purse(p1, _);
        short b1 = p1.balance;
        //@ close purse(p1, b1);
        //@ open purse(p2, _);
        short b2 = p2.balance;
        //@ close purse(p2, b2);
        assert b1 == 100 && b2 == 50;
    }
}