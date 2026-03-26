/*@ predicate dummy() = true; @*/

class Program {
    //@ requires true;
    //@ ensures result <= x &*& result <= y &*& result <= z;
    //@ ensures (result == x || result == y || result == z);
    static short min(short x, short y, short z)
    {
        short m = (x < y ? x : y);
        m = (m < z ? m : z);
        return m;
    }
}