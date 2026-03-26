public class LeftPad {

    static char[] leftPad(char c, int n, char[] s)
    //@ requires s != null;
    //@ ensures result != null;
    {
        int pad = Math.max(n - s.length, 0);
        //@ assert pad >= 0;
        char[] v = new char[pad + s.length];
        //@ close array<char>(v, _);
        int i = 0;

        for(; ; i++)
        //@ invariant 0 <= i && i <= pad;
        //@ invariant array<char>(v, _);
        {
            if (i == pad) {
                //@ open array<char>(v, _);
                break;
            }
            //@ open array<char>(v, _);
            v[i] = c;
            //@ close array<char>(v, _);
        }
        
        for(; ; i++)
        //@ invariant pad <= i && i <= v.length;
        //@ invariant array<char>(v, _);
        {
            if (i == v.length) {
                //@ open array<char>(v, _);
                break;
            }
            //@ open array<char>(v, _);
            v[i] = s[i - pad];
            //@ close array<char>(v, _);
        }
        
        //@ close array<char>(v, _);
        return v;
    }
    
}