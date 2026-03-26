class Purse {
    short balance;
}

/*@

predicate purse(Purse p; short b) =
    p != null &*& p.balance |-> b;

@*/

class Program {
    Purse p1, p2;

    //@ requires purse(p, ?b);
    //@ ensures purse(p, (short)(b + amount));
    void deposit(Purse p, short amount)
    {
        //@ open purse(p, b);
        p.balance += amount;
        //@ close purse(p, (short)(b + amount));
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

        //@ open purse(p1, (short)100);
        short b1 = p1.balance;
        //@ close purse(p1, (short)100);
        //@ open purse(p2, (short)50);
        short b2 = p2.balance;
        //@ close purse(p2, (short)50);
        assert b1 == 100 && b2 == 50;
    }
}