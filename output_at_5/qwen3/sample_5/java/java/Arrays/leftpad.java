public class LeftPad {

    static char[] leftPad(char c, int n, char[] s)
        //@ requires true;
        //@ ensures result != null &*& \result.length == Math.max(n - s.length, 0) + s.length;
    {
        int pad = Math.max(n - s.length, 0);
        char[] v = new char[pad + s.length];
        int i = 0;

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
        
        return v;
    }
    
}