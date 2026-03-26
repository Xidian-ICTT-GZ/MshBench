class Purse {
    short balance;
}

/*@
predicate purse(Purse p; short b) = p.balance |-> b;
@*/

class Program {
    Purse p1, p2;

    //@ requires purse(p, ?old) &*& Short.MIN_VALUE <= old + amount &*& old + amount <= Short.MAX_VALUE;
    //@ ensures purse(p, (short)(old + amount));
    void deposit(Purse p, short amount)
    {
        //@ open purse(p, old);
        p.balance += amount;
        //@ close purse(p, (short)(old + amount));
    }

    //@ requires true;
    //@ ensures purse(p1, 100) &*& purse(p2, 50);
    Program()
    {
        p1 = new Purse();
        //@ close purse(p1, 0);
        deposit(p1, (short) 100);
        p2 = new Purse();
        //@ close purse(p2, 0);
        deposit(p2, (short) 50);

        //@ open purse(p1, b1);
        short b1 = p1.balance;
        //@ close purse(p1, b1);
        //@ open purse(p2, b2);
        short b2 = p2.balance;
        //@ close purse(p2, b2);
        assert b1 == 100 && b2 == 50;
    }
}