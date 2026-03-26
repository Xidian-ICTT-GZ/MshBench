public class LeftPad {

    /*@
    predicate char_array(char[] a; int len) =
        a != null &*& a.length == len &*& chars(a, 0, len, _);
    @*/

    static char[] leftPad(char c, int n, char[] s)
    //@ requires char_array(s, ?len) &*& n >= 0;
    //@ ensures char_array(result, ?resLen) &*& resLen == (n > len ? n : len);
    {
        int pad = Math.max(n - s.length, 0);
        char[] v = new char[pad + s.length];
        //@ close char_array(v, pad + s.length);
        int i = 0;

        //@ open char_array(v, pad + s.length);
        for(; ; i++)
        //@ invariant 0 <= i &*& i <= pad &*& chars(v, 0, i, _) &*& chars(v, i, pad + s.length, _);
        {
            if (i == pad) {
                break;
            }
            
            v[i] = c;
        }
        
        for(; ; i++)
        //@ invariant pad <= i &*& i <= pad + s.length &*& chars(v, 0, pad, _) &*& chars(v, pad, i, _) &*& chars(v, i, pad + s.length, _) &*& char_array(s, s.length);
        {
            
            if (i == v.length) {
                break;
            }
            v[i] = s[i - pad];
        }
        //@ close char_array(v, pad + s.length);
        return v;
    }
    
}