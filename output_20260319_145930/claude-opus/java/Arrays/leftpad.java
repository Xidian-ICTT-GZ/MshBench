public class LeftPad {

    static char[] leftPad(char c, int n, char[] s)
    //@ requires s != null &*& array_slice(s, 0, s.length, _);
    //@ ensures result != null &*& array_slice(result, 0, result.length, _) &*& array_slice(s, 0, s.length, _);
    {
        int pad = Math.max(n - s.length, 0);
        char[] v = new char[pad + s.length];
        int i = 0;

        for(; ; i++)
        //@ invariant v != null &*& s != null &*& 0 <= i &*& i <= pad &*& array_slice(v, 0, v.length, _) &*& array_slice(s, 0, s.length, _) &*& v.length == pad + s.length;
        {
            if (i == pad) {
                
                
                break;
            }
            
            v[i] = c;
        }
        
        for(; ; i++)
        //@ invariant v != null &*& s != null &*& pad <= i &*& i <= v.length &*& array_slice(v, 0, v.length, _) &*& array_slice(s, 0, s.length, _) &*& v.length == pad + s.length;
        {
            
            if (i == v.length) {
                
                
                break;
            }
            v[i] = s[i - pad];
        }
        
        return v;
    }
    
}