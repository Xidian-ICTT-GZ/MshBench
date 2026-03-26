public class LeftPad {

    /*@
    predicate chars(char[] a, int length) =
        a != null &*& length == a.length;
    @*/

    //@ requires s != null &*& chars(s, s.length);
    //@ ensures result != null &*& chars(result, result.length);
    static char[] leftPad(char c, int n, char[] s)
    {
        int pad = Math.max(n - s.length, 0);
        char[] v = new char[pad + s.length];
        int i = 0;

        //@ loop_invariant 0 <= i && i <= pad &*& chars(v, v.length);
        for(; ; i++)
        {
            if (i == pad) {
                break;
            }
            v[i] = c;
        }
        
        //@ loop_invariant pad <= i && i <= v.length &*& chars(v, v.length);
        for(; ; i++)
        {
            if (i == v.length) {
                break;
            }
            v[i] = s[i - pad];
        }
        
        return v;
    }
    
}