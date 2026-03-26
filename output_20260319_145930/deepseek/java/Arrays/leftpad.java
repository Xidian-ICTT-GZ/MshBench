public class LeftPad {

    //@ predicate charArray(char[] arr, int length) = arr != null &*& arr.length == length &*& chars(arr, 0, length, _);
    
    static char[] leftPad(char c, int n, char[] s)
    //@ requires charArray(s, ?slen);
    //@ ensures charArray(result, ?rlen) &*& rlen == Math.max(n, slen);
    {
        int pad = Math.max(n - s.length, 0);
        char[] v = new char[pad + s.length];
        //@ close charArray(v, pad + s.length);
        //@ chars_split(v, 0, pad);
        //@ chars_split(v, pad, pad + s.length);
        int i = 0;

        for(; ; i++)
        //@ invariant 0 <= i &*& i <= pad &*& chars(v, 0, i, ?cs1) &*& chars(v, i, pad, _) &*& chars(v, pad, pad + s.length, _);
        {
            if (i == pad) {
                //@ close chars(v, i, pad, _);
                break;
            }
            
            v[i] = c;
            //@ chars_join(v);
        }
        
        for(; ; i++)
        //@ invariant pad <= i &*& i <= pad + s.length &*& chars(v, 0, pad, ?cs1) &*& chars(v, pad, i, ?cs2) &*& chars(v, i, pad + s.length, _) &*& charArray(s, slen);
        {
            
            if (i == v.length) {
                //@ close chars(v, i, pad + s.length, _);
                break;
            }
            v[i] = s[i - pad];
            //@ chars_join(v);
        }
        
        //@ chars_join(v);
        //@ close charArray(v, pad + s.length);
        //@ assert pad + s.length == Math.max(n, s.length);
        return v;
    }
    
}