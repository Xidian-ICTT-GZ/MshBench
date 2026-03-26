/*@ predicate char_array(char[] a; int len) = 
    a != null &*& [?f]a |-> ?contents &*& array_slice(a, 0, len, contents); @*/

public class LeftPad {

    //@ requires c_::char &*& n >= 0 &*& s != null &*& char_array(s, ?s_len);
    //@ ensures char_array(result, ?res_len) &*& res_len == (n > s_len ? n : s_len);
    static char[] leftPad(char c, int n, char[] s)
    {
        int pad = Math.max(n - s.length, 0);
        char[] v = new char[pad + s.length];
        int i = 0;

        //@ invariant 0 <= i &*& i <= pad &*& char_array(v, pad + s.length) &*& char_array(s, s.length);
        for(; ; i++)
        {
            if (i == pad) {
                break;
            }
            v[i] = c;
        }
        
        //@ invariant pad <= i &*& i <= pad + s.length &*& char_array(v, pad + s.length) &*& char_array(s, s.length);
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