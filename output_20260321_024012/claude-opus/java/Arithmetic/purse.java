class Purse {
    /*@
    predicate purse_state(short balance) = this.balance |-> balance;
    @*/
    short balance;
}

class Program {
    Purse p1, p2;

    void deposit(Purse p, short amount)
        //@ requires p.purse_state(?b);
        //@ ensures p.purse_state((short)(b + amount));
    {
        //@ open p.purse_state(?b);
        p.balance += amount;
        //@ close p.purse_state((short)(b + amount));
    }

    Program()
        //@ requires true;
        //@ ensures true;
    {
        p1 = new Purse();
        //@ close p1.purse_state((short)0);
        deposit(p1, (short)100);

        p2 = new Purse();
        //@ close p2.purse_state((short)0);
        deposit(p2, (short)50);

        short b1 = p1.balance;
        short b2 = p2.balance;
        assert b1 == 100 && b2 == 50;
    }
}