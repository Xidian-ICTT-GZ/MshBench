public class LeftPad {

    static char[] leftPad(char c, int n, char[] s)
    //@ requires s != null &*& Integer.MIN_VALUE + s.length <= n;
    //@ ensures result != null;
    {
        int pad = Math.max(n - s.length, 0);
        char[] v = new char[pad + s.length];
        int i = 0;

        for(; ; i++)
        //@ invariant 0 <= i &*& i <= pad &*& v != null &*& s != null &*& 0 <= pad;
        {
            if (i == pad) {
                
                
                break;
            }
            
            v[i] = c;
        }
        
        for(; ; i++)
        //@ invariant pad <= i &*& i <= v.length &*& v != null &*& s != null &*& 0 <= pad;
        {
            
            if (i == v.length) {
                
                
                break;
            }
            v[i] = s[i - pad];
        }
        
        return v;
    }
    
}