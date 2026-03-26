class Purse {
    short balance;
}

/*@
predicate purse(Purse p; int b) = p.balance |-> (short)b;
@*/

class Program {
    Purse p1, p2;

    void deposit(Purse p, short amount)
        //@ requires purse(p, ?b) &*& -32768 <= b + (int)amount &*& b + (int)amount <= 32767;
        //@ ensures purse(p, b + (int)amount);
        
    {
        //@ open purse(p, b);
        p.balance += amount;
        //@ close purse(p, b + (int)amount);
    }

    Program()
        //@ requires true;
        //@ ensures true;
        
    {
        p1 = new Purse();
        //@ close purse(p1, 0);
        deposit(p1, (short)100);
        p2 = new Purse();
        //@ close purse(p2, 0);
        deposit(p2, (short)50);

        //@ open purse(p1, ?b1g);
        short b1 = p1.balance;
        //@ open purse(p2, ?b2g);
        short b2 = p2.balance;
        //@ assert b1g == 100;
        //@ assert b2g == 50;
        assert b1 == 100 && b2 == 50;
        //@ close purse(p2, b2g);
        //@ close purse(p1, b1g);
    }
}