/*@ predicate purse(Purse p, short bal) = p.balance |-> bal; @*/

class Purse {
    short balance;
}

class Program {
    Purse p1, p2;

    //@ requires purse(p, ?old_bal) &*& amount >= 0 &*& old_bal >= 0 &*& (short)(old_bal + amount) == old_bal + amount;
    //@ ensures purse(p, old_bal + amount);
    void deposit(Purse p, short amount)
        
        
    {
        p.balance += amount;
    }

    //@ requires true;
    //@ ensures purse(p1, 100) &*& purse(p2, 50);
    Program()
        
        
    {
        p1 = new Purse();
        /*@ close purse(p1, 0); @*/
        deposit(p1, (short)100);
        p2 = new Purse();
        /*@ close purse(p2, 0); @*/
        deposit(p2, (short)50);

        short b1 = p1.balance;
        short b2 = p2.balance;
        assert b1 == 100 && b2 == 50;
    }
}