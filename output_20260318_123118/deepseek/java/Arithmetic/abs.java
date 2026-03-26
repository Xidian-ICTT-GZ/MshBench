class Program {
//@ requires -32768 <= x &*& x <= 32767;
//@ ensures 0 <= result &*& (x < 0 ? result == -x : result == x);
static int abs(short x)
        
        
    {
        if (x < 0)
            return -x;
        else
            return x;
    }
}