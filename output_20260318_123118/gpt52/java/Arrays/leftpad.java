public class LeftPad {

    /*@ predicate chars(char[] a; int n) =
            a != null &*& a.length == n;
    @*/

    static char[] leftPad(char c, int n, char[] s)
    //@ requires chars(s, ?len);
    //@ ensures chars(result, ?rlen);
    {
        int pad = Math.max(n - s.length, 0);
        char[] v = new char[pad + s.length];
        int i = 0;

        for(; ; i++)
        //@ invariant chars(s, len) &*& chars(v, pad + len) &*& 0 <= i &*& i <= pad;
        {
            if (i == pad) {
                break;
            }

            v[i] = c;
        }

        for(; ; i++)
        //@ invariant chars(s, len) &*& chars(v, pad + len) &*& pad <= i &*& i <= v.length;
        {
            if (i == v.length) {
                break;
            }
            v[i] = s[i - pad];
        }

        return v;
    }

}