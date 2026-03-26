class Purse {
    short balance;
    /*@
    predicate purse(short b) = this.balance |-> b;
    @*/
}

class Program {
    Purse p1, p2;

    void deposit(Purse p, short amount)
        //@ requires p != null &*& p.purse(?b);
        //@ ensures p.purse((short)(b + amount));
        
    {
        //@ open p.purse(b);
        p.balance += amount;
        //@ close p.purse((short)(b + amount));
    }

    Program()
        //@ requires true;
        //@ ensures true;
        
    {
        p1 = new Purse();
        //@ close p1.purse((short)0);
        deposit(p1, (short)100);
        p2 = new Purse();
        //@ close p2.purse((short)0);
        deposit(p2, (short)50);

        //@ open p1.purse(?b1g);
        short b1 = p1.balance;
        //@ close p1.purse(b1g);
        //@ open p2.purse(?b2g);
        short b2 = p2.balance;
        //@ close p2.purse(b2g);
        assert b1 == 100 && b2 == 50;
    }
}