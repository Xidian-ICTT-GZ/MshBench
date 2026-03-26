class Purse {
    short balance;
}

/*@ predicate purse(Purse p; short b) =
        p != null &*& p.balance |-> b;
@*/

class Program {
    Purse p1, p2;

    void deposit(Purse p, short amount)
        //@ requires purse(p, ?b) &*& (short)(b + amount) == b + amount;
        //@ ensures purse(p, (short)(b + amount));
    {
        p.balance += amount;
    }

    Program()
        //@ requires true;
        //@ ensures true;
    {
        p1 = new Purse();
        //@ assume(p1 != null);
        //@ close purse(p1, (short)0);
        deposit(p1, (short)100);
        p2 = new Purse();
        //@ assume(p2 != null);
        //@ close purse(p2, (short)0);
        deposit(p2, (short)50);

        //@ open purse(p1, (short)100);
        short b1 = p1.balance;
        //@ close purse(p1, (short)100);
        //@ open purse(p2, (short)50);
        short b2 = p2.balance;
        //@ close purse(p2, (short)50);
        assert b1 == 100 && b2 == 50;
        //@ open purse(p2, (short)50);
        //@ open purse(p1, (short)100);
    }
}