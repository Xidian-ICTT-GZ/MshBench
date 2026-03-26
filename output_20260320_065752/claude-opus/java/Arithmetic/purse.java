class Purse {
    short balance;

    /*@
    predicate purse(Purse p, short b) = p.balance |-> b;
    @*/
}

class Program {
    Purse p1, p2;

    //@ requires pursep(?p, ?b);
    //@ ensures pursep(p, (short)(b + amount));
    void deposit(Purse p, short amount)
    //@ requires purse(p, ?b);
    //@ ensures purse(p, (short)(b + amount));
    {
        //@ open purse(p, b);
        p.balance += amount;
        //@ close purse(p, (short)(b + amount));
    }

    //@ requires true;
    //@ ensures pursep(p1, 100) &*& pursep(p2, 50);
    Program()
    {
        p1 = new Purse();
        //@ close purse(p1, 0);
        deposit(p1, (short)100);
        p2 = new Purse();
        //@ close purse(p2, 0);
        deposit(p2, (short)50);

        //@ open purse(p1, ?b1);
        //@ open purse(p2, ?b2);
        short b1 = p1.balance;
        short b2 = p2.balance;
        assert b1 == 100 && b2 == 50;
        //@ close purse(p1, b1);
        //@ close purse(p2, b2);
    }
}