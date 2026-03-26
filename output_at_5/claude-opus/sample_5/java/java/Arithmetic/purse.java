class Purse {
    short balance;

    /*@
    predicate purse(int b) = this.balance |-> b;
    @*/
}

class Program {
    Purse p1, p2;

    void deposit(Purse p, short amount)
        //@ requires p.purse(?bal);
        //@ ensures p.purse(bal + amount);
    {
        //@ open p.purse(bal);
        p.balance = (short)(bal + amount);
        //@ close p.purse(bal + amount);
    }

    Program()
        //@ requires true;
        //@ ensures true;
    {
        p1 = new Purse();
        p1.balance = 0;
        //@ close p1.purse(0);
        deposit(p1, (short)100);

        p2 = new Purse();
        p2.balance = 0;
        //@ close p2.purse(0);
        deposit(p2, (short)50);

        //@ open p1.purse(?bal1);
        short b1 = p1.balance;
        //@ close p1.purse(bal1);

        //@ open p2.purse(?bal2);
        short b2 = p2.balance;
        //@ close p2.purse(bal2);

        assert b1 == 100 && b2 == 50;
    }
}