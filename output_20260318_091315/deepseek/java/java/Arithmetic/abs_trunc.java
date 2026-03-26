class Program {
    //@ requires -32768 <= x && x <= 32767;
    //@ ensures 0 <= result && result <= 32767;
    //@ ensures x < 0 ? result == -x : result == x;
    static short abs(short x)
        
        
    {
        if (x < 0) {
            x = (short)-x;
            return x;
        } else {
            return x;
        }
    }
}