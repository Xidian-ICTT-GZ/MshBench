class Purse {
    short balance;
}

/*@
predicate Purse(Purse p; short balance) =
    p.balance |-> balance;
@*/

class Program {
    Purse p1, p2;

    void deposit(Purse p, short amount)
        //@ requires Purse(p, ?b);
        //@ ensures Purse(p, (short)(b + amount));
    {
        //@ open Purse(p, b);
        p.balance += amount;
        //@ close Purse(p, (short)(b + amount));
    }

    Program()
        //@ requires true;
        //@ ensures true;
    {
        p1 = new Purse();
        //@ close Purse(p1, 0);
        deposit(p1, (short)100);
        p2 = new Purse();
        //@ close Purse(p2, 0);
        deposit(p2, (short)50);

        //@ open Purse(p1, _);
        short b1 = p1.balance;
        //@ open Purse(p2, _);
        short b2 = p2.balance;
        assert b1 == 100 && b2 == 50;
    }
}