public class LeftPad {

    //@ requires s != null && n >= 0;
    //@ ensures result != null && result.length >= n && result.length == (n > s.length ? n : s.length);
    //@ ensures (\forall int k; 0 <= k && k < result.length; 
    //@             (k < n - s.length ? result[k] == c : result[k] == s[k - (n - s.length)]));
    static char[] leftPad(char c, int n, char[] s)
    {
        int pad = Math.max(n - s.length, 0);
        char[] v = new char[pad + s.length];
        int i = 0;

        for(; ; i++)
        //@ invariant 0 <= i && i <= pad && v.length == pad + s.length;
        {
            if (i == pad) {
                break;
            }
            v[i] = c;
        }
        
        for(; ; i++)
        //@ invariant pad <= i && i <= v.length && v.length == pad + s.length;
        {
            if (i == v.length) {
                break;
            }
            v[i] = s[i - pad];
        }
        
        return v;
    }
    
}