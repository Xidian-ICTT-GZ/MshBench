class Purse {
    short balance;
    /*@
    predicate purse_inv() = this |-> balance;
    @*/
}

class Program {
    Purse p1, p2;

    void deposit(Purse p, short amount)
        //@ requires p.purse_inv();
        //@ ensures p.purse_inv();
    {
        //@ open p.purse_inv();
        p.balance += amount;
        //@ close p.purse_inv();
    }

    Program()
        //@ requires true;
        //@ ensures true;
    {
        p1 = new Purse();
        //@ close p1.purse_inv();
        deposit(p1, (short)100);
        p2 = new Purse();
        //@ close p2.purse_inv();
        deposit(p2, (short)50);

        short b1 = p1.balance;
        short b2 = p2.balance;
        //@ open p1.purse_inv();
        //@ open p2.purse_inv();
        assert b1 == 100 && b2 == 50;
        //@ close p1.purse_inv();
        //@ close p2.purse_inv();
    }
}