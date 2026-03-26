/*@ predicate charArray(char[] a; int len) = a != null &*& [?f]a |-> ?contents &*& length(a) == len &*& chars(a, 0, len, contents); @*/

public class LeftPad {

    //@ requires s != null &*& n >= 0 &*& charArray(s, ?s_len);
    //@ ensures charArray(result, ?res_len) &*& res_len == (n > s.length ? n : s.length);
    static char[] leftPad(char c, int n, char[] s)
    {
        int pad = Math.max(n - s.length, 0);
        char[] v = new char[pad + s.length];
        int i = 0;

        //@ loop invariant 0 <= i &*& i <= pad &*& charArray(v, pad + s.length) &*& charArray(s, s.length);
        //@ loop invariant forall(int j; 0 <= j &*& j < i ==> v[j] == c);
        for(; ; i++)
        {
            if (i == pad) {
                break;
            }
            v[i] = c;
        }
        
        //@ loop invariant pad <= i &*& i <= pad + s.length &*& charArray(v, pad + s.length) &*& charArray(s, s.length);
        //@ loop invariant forall(int j; 0 <= j &*& j < pad ==> v[j] == c) &*&
        //@           forall(int j; pad <= j &*& j < i ==> v[j] == s[j - pad]);
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