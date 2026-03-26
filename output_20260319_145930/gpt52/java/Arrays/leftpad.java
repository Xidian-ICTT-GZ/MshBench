public class LeftPad {

    /*@
    predicate chars(char[] a; int n) =
        a != null &*& a.length == n &*& chars(a, 0, n, _);
    @*/

    //@ requires s != null &*& chars(s, s.length);
    //@ ensures chars(result, result.length) &*& s != null &*& chars(s, s.length);
    static char[] leftPad(char c, int n, char[] s)
    {
        int pad = Math.max(n - s.length, 0);
        char[] v = new char[pad + s.length];
        //@ close chars(v, v.length);
        int i = 0;

        for(; ; i++)
        //@ invariant chars(v, v.length) &*& chars(s, s.length) &*& 0 <= i &*& i <= pad;
        {
            if (i == pad) {
                break;
            }
            v[i] = c;
        }

        for(; ; i++)
        //@ invariant chars(v, v.length) &*& chars(s, s.length) &*& pad <= i &*& i <= v.length;
        {
            if (i == v.length) {
                break;
            }
            v[i] = s[i - pad];
        }

        return v;
    }

}