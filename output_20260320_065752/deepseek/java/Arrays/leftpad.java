public class LeftPad {

    //@ requires n >= 0 &*& s != null;
    //@ ensures result != null;
    static char[] leftPad(char c, int n, char[] s)
    
    

    {
        //@ close array_slice(s, 0, s.length, _);
        //@ close array_slice_char(s, 0, s.length, _);
        int pad = Math.max(n - s.length, 0);
        //@ assert pad >= 0;
        char[] v = new char[pad + s.length];
        //@ close array_slice(v, 0, v.length, _);
        //@ close array_slice_char(v, 0, v.length, _);
        int i = 0;

        //@ loop_invariant 0 <= i &*& i <= pad;
        //@ loop_invariant array_slice_char(v, 0, i, _);
        //@ loop_invariant array_slice_char(v, i, v.length, _);
        for(; ; i++)
        
        
        {
            if (i == pad) {
                
                
                break;
            }
            //@ open array_slice_char(v, i, v.length, _);
            //@ open array_slice_char(v, i, 1, _);
            v[i] = c;
            //@ close array_slice_char(v, i, 1, _);
            //@ close array_slice_char(v, i+1, v.length - (i+1), _);
        }
        //@ assert i == pad;
        //@ assert array_slice_char(v, 0, pad, _);
        //@ assert array_slice_char(v, pad, v.length - pad, _);
        
        //@ loop_invariant pad <= i &*& i <= v.length;
        //@ loop_invariant array_slice_char(v, 0, pad, _);
        //@ loop_invariant array_slice_char(v, pad, i - pad, _);
        //@ loop_invariant array_slice_char(v, i, v.length - i, _);
        for(; ; i++)
        
        
        {
            
            if (i == v.length) {
                
                
                break;
            }
            //@ open array_slice_char(v, i, v.length - i, _);
            //@ open array_slice_char(v, i, 1, _);
            //@ open array_slice_char(s, i - pad, s.length - (i - pad), _);
            //@ open array_slice_char(s, i - pad, 1, _);
            v[i] = s[i - pad];
            //@ close array_slice_char(s, i - pad, 1, _);
            //@ close array_slice_char(s, i - pad + 1, s.length - (i - pad + 1), _);
            //@ close array_slice_char(v, i, 1, _);
            //@ close array_slice_char(v, i+1, v.length - (i+1), _);
        }
        //@ open array_slice_char(v, 0, v.length, _);
        //@ open array_slice(s, 0, s.length, _);
        //@ open array_slice_char(s, 0, s.length, _);
        //@ open array_slice(v, 0, v.length, _);
        return v;
    }
    
}