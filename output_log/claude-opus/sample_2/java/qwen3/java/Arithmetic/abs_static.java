class Program {
    /*@ lemma void abs_nonnegative(short x)
        requires true;
        ensures result >= 0 &*& (x >= 0 ==> result == x) &*& (x < 0 ==> result == -x);
    {
        if (x < 0) {
            assert result == -x;
            assert result >= 0;
        } else {
            assert result == x;
            assert result >= 0;
        }
    } @*/

    static short abs(short x)
    //@ requires true;
    //@ ensures result >= 0 &*& (x >= 0 ==> result == x) &*& (x < 0 ==> result == -x);
    {
        if (x < 0) {
            x = (short) -x;
            return x;
        } else {
            return x;
        }
    }
}