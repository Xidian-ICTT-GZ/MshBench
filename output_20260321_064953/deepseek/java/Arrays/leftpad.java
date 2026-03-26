public class LeftPad {

    //@ requires n >= 0;
    //@ requires s != null;
    //@ ensures result != null;
    //@ ensures result.length == Math.max(n, s.length);
    static char[] leftPad(char c, int n, char[] s)
    
    

    {
        //@ close arraychars(s, s.length);
        int pad = Math.max(n - s.length, 0);
        //@ assert pad >= 0;
        char[] v = new char[pad + s.length];
        //@ close arraychars(v, v.length);
        int i = 0;

        //@ loop_invariant 0 <= i && i <= pad;
        //@ loop_invariant arraychars(v, v.length);
        //@ loop_invariant chars(v, 0, i, c);
        //@ loop_invariant chars(v, i, v.length, _);
        for(; ; i++)
        
        
        {
            if (i == pad) {
                
                
                break;
            }
            //@ open arraychars(v, v.length);
            //@ open chars(v, i, v.length, _);
            v[i] = c;
            //@ close chars(v, i, i+1, c);
            //@ close chars(v, i+1, v.length, _);
            //@ close arraychars(v, v.length);
        }
        //@ assert i == pad;
        //@ assert chars(v, 0, pad, c);
        
        //@ loop_invariant pad <= i && i <= v.length;
        //@ loop_invariant arraychars(v, v.length);
        //@ loop_invariant chars(v, 0, pad, c);
        //@ loop_invariant chars(v, pad, i, s, 0);
        //@ loop_invariant chars(v, i, v.length, _);
        for(; ; i++)
        
        
        {
            
            if (i == v.length) {
                
                
                break;
            }
            //@ open arraychars(v, v.length);
            //@ open chars(v, i, v.length, _);
            //@ open arraychars(s, s.length);
            //@ open chars(s, i-pad, s.length, _);
            v[i] = s[i - pad];
            //@ close chars(s, i-pad, s.length, _);
            //@ close arraychars(s, s.length);
            //@ close chars(v, i, i+1, s[i-pad]);
            //@ close chars(v, i+1, v.length, _);
            //@ close arraychars(v, v.length);
        }
        //@ open arraychars(v, v.length);
        //@ open chars(v, v.length, v.length, _);
        //@ close arraychars(v, v.length);
        return v;
    }
    
    //@ predicate arraychars(char[] a, int n) = chars(a, 0, n, _);
    
    /*@
    predicate chars(char[] a, int m, int n, char c) =
        m == n ? true : character(&a[m], c) &*& chars(a, m+1, n, c);
    predicate chars(char[] a, int m, int n, char[] src, int srcOff) =
        n <= m ? true : character(&a[m], src[srcOff]) &*& chars(a, m+1, n, src, srcOff+1);
    @*/
    
}