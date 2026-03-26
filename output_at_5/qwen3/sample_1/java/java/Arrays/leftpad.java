public class LeftPad {

    static char[] leftPad(char c, int n, char[] s)
        //@ requires true;
        //@ ensures result != null &*& arrayContent(result, 0, pad + s.length, (char[])null);
        //@ ensures \forall int i; 0 <= i < pad ==> result[i] == c;
        //@ ensures \forall int i; pad <= i < pad + s.length ==> result[i] == s[i - pad];
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