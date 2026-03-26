public class LeftPad {

    /*@
    predicate char_array(char[] a, int length) =
        a != null &*& a.length == length;
    @*/

    static char[] leftPad(char c, int n, char[] s)
    //@ requires char_array(s, ?len) &*& n >= 0;
    //@ ensures char_array(result, ?resLen) &*& resLen == (n > len ? n : len);
    {
        int pad = Math.max(n - s.length, 0);
        char[] v = new char[pad + s.length];
        //@ close char_array(v, pad + s.length);
        int i = 0;

        //@ open char_array(v, _);
        for(; ; i++)
        {
            if (i == pad) {
                break;
            }
            v[i] = c;
        }

        for(; ; i++)
        {
            if (i == v.length) {
                break;
            }
            v[i] = s[i - pad];
        }
        //@ close char_array(v, v.length);

        return v;
    }

}