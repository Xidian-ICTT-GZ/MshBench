class Purse {
    short balance;
    
    /*@
    predicate purse(?b) = this.balance |-> b;
    @*/
}

class Program {
    Purse p1, p2;

    void deposit(Purse p, short amount)
        //@ requires p.purse(?b);
        //@ ensures p.purse(b + amount);
    {
        //@ open p.purse(?b);
        p.balance += amount;
        //@ close p.purse(b + amount);
    }

    Program()
        //@ requires true;
        //@ ensures true;
    {
        p1 = new Purse();
        //@ close p1.purse(0);
        deposit(p1, (short)100);

        p2 = new Purse();
        //@ close p2.purse(0);
        deposit(p2, (short)50);

        //@ open p1.purse(?b1);
        //@ open p2.purse(?b2);
        short b1 = p1.balance;
        short b2 = p2.balance;
        assert b1 == 100 && b2 == 50;
        //@ close p1.purse(b1);
        //@ close p2.purse(b2);
    }
}