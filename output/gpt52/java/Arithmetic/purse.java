class Purse {
    short balance;
    /*@ predicate purse(short b) = this.balance |-> b; @*/
}

class Program {
    Purse p1, p2;

    void deposit(Purse p, short amount)
    //@ requires p != null &*& p.balance |-> ?b;
    //@ ensures p.balance |-> (short)(b + amount);
    {
        p.balance += amount;
    }

    Program()
    //@ requires true;
    //@ ensures true;
    {
        p1 = new Purse();
        //@ open p1.purse(?b0);
        //@ close p1.purse((short)0);
        //@ open p1.purse(?b1);
        deposit(p1, (short) 100);
        //@ close p1.purse((short)100);
        p2 = new Purse();
        //@ open p2.purse(?b2);
        //@ close p2.purse((short)0);
        //@ open p2.purse(?b3);
        deposit(p2, (short) 50);
        //@ close p2.purse((short)50);

        //@ open p1.purse(?pb1);
        short b1 = p1.balance;
        //@ close p1.purse(pb1);
        //@ open p2.purse(?pb2);
        short b2 = p2.balance;
        //@ close p2.purse(pb2);
        assert b1 == 100 && b2 == 50;
    }
}