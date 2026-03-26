class Purse {
    short balance;
}

/*@
predicate purse(Purse p; short b) = p.balance |-> b;
@*/

class Program {
    Purse p1, p2;

    void deposit(Purse p, short amount)
        //@ requires purse(p, ?b);
        //@ ensures purse(p, (short)(b + amount));
        
    {
        //@ open purse(p, b);
        p.balance += amount;
        //@ close purse(p, (short)(b + amount));
    }

    Program()
        //@ requires true;
        //@ ensures true;
        
    {
        p1 = new Purse();
        //@ close purse(p1, (short)0);
        deposit(p1, (short)100);
        p2 = new Purse();
        //@ close purse(p2, (short)0);
        deposit(p2, (short)50);

        //@ open purse(p1, ?b1g);
        short b1 = p1.balance;
        //@ open purse(p2, ?b2g);
        short b2 = p2.balance;
        //@ assert b1 == b1g;
        //@ assert b2 == b2g;
        //@ assert b1g == (short)100;
        //@ assert b2g == (short)50;
        assert b1 == 100 && b2 == 50;
        //@ close purse(p2, b2g);
        //@ close purse(p1, b1g);
    }
}