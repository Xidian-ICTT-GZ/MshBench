public class LeftPad {

    /*@
    predicate charArray(char[] a; int len) =
        a != null &*& a.length == len &*& chars(a, 0, len, _);
    @*/

    static char[] leftPad(char c, int n, char[] s)
    //@ requires charArray(s, ?s_len) &*& n >= 0;
    //@ ensures charArray(result, ?res_len) &*& res_len == (n > s_len ? n : s_len);
    {
        int pad = Math.max(n - s.length, 0);
        char[] v = new char[pad + s.length];
        //@ close charArray(v, pad + s.length);
        int i = 0;

        for(; ; i++)
        //@ invariant 0 <= i &*& i <= pad &*& charArray(v, pad + s.length) &*& charArray(s, s.length);
        {
            if (i == pad) {
                break;
            }
            v[i] = c;
        }
        
        for(; ; i++)
        //@ invariant pad <= i &*& i <= pad + s.length &*& charArray(v, pad + s.length) &*& charArray(s, s.length);
        {
            if (i == v.length) {
                break;
            }
            v[i] = s[i - pad];
        }
        
        return v;
    }
    
}