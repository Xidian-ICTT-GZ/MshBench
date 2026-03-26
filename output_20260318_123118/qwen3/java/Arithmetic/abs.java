class Program {
    /*@ predicate true_pred() = true; @*/

    //@ requires true;
    //@ ensures result >= 0 &*& (x >= 0 ? result == x : result == -x);
    //@ ensures (x >= 0) ==> (result == x);
    //@ ensures (x < 0) ==> (result == -x);
    static int abs(short x)
        
        
    {
        if (x < 0)
            return -x;
        else
            return x;
    }
}