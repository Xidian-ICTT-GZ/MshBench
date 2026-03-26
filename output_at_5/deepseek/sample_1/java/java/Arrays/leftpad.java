public class LeftPad {

    //@ requires n >= 0;
    //@ requires s != null;
    //@ ensures result != null;
    //@ ensures result.length == Math.max(n, s.length);
    static char[] leftPad(char c, int n, char[] s)
    
    

    {
        int pad = Math.max(n - s.length, 0);
        //@ assert pad >= 0;
        char[] v = new char[pad + s.length];
        //@ assert v != null;
        //@ assert v.length == pad + s.length;
        int i = 0;

        //@ loop_invariant 0 <= i && i <= pad;
        //@ loop_invariant i <= v.length;
        for(; ; i++)
        
        
        {
            if (i == pad) {
                
                
                break;
            }
            
            v[i] = c;
        }
        
        //@ loop_invariant pad <= i && i <= v.length;
        //@ loop_invariant pad == Math.max(n - s.length, 0);
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