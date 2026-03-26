class Purse {
    short balance;
}

class Program {
    Purse p1, p2;

    //@ requires p != null &*& p.balance |-> ?v &*& v + amount >= -32768 &*& v + amount <= 32767;
    //@ ensures p != null &*& p.balance |-> (short)(v + amount);
    void deposit(Purse p, short amount)

    {
        p.balance += amount;
    }

    //@ requires true;
    //@ ensures this.p1 |-> ?purse1 &*& this.p2 |-> ?purse2 &*& purse1 != null &*& purse2 != null &*& purse1.balance |-> 100 &*& purse2.balance |-> 50;
    Program()

    {
        p1 = new Purse();
        //@ close p1.balance |-> 0;
        deposit(p1, (short) 100);
        p2 = new Purse();
        //@ close p2.balance |-> 0;
        deposit(p2, (short) 50);

        short b1 = p1.balance;
        short b2 = p2.balance;
        assert b1 == 100 && b2 == 50;
    }
}