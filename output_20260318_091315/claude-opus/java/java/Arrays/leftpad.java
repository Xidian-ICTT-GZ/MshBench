public class LeftPad {

    /*@ 
      predicate array_char(char[] a; int length) = 
        a != null &*& 0 <= length &*& length <= a.length &*&
        chars(a, 0, length, ?cs);

      predicate chars(char[] a, int start, int end, list<char> cs) = start == end ? 
        cs == nil :
        chars(a, start + 1, end, ?rest) &*& a[start] |-> ?ch &*& cs == cons(ch, rest);
    @*/

    //@ requires s != null &*& 0 <= n &*& array_char(s, s.length);
    //@ ensures result != null &*& result.length >= n &*& array_char(result, result.length);
    //@ ensures chars(result, 0, result.length, ?cs);
    //@ ensures length(cs) == result.length &*& 
    //@         (forall int i; 0 <= i &*& i < pad ==> nth(cs, i) == c) &*&
    //@         (forall int i; pad <= i &*& i < result.length ==> nth(cs, i) == s[i - pad]);
    static char[] leftPad(char c, int n, char[] s)
    {
        int pad = Math.max(n - s.length, 0);
        /*@ 
          // pad >= 0 &*& pad == n - s.length || pad == 0 &*& n < s.length;
          @*/
        char[] v = new char[pad + s.length];
        //@ array_char(v, v.length);
        int i = 0;

        /*@ loop_invariant 0 <= i &*& i <= pad &*& 
            array_char(v, v.length) &*& array_char(s, s.length) &*&
            (forall int j; 0 <= j &*& j < i ==> v[j] == c);
        @*/
        for(; ; i++)
        {
            if (i == pad) {
                break;
            }
            
            v[i] = c;
        }

        /*@ loop_invariant pad <= i &*& i <= v.length &*&
            array_char(v, v.length) &*& array_char(s, s.length) &*&
            (forall int j; 0 <= j &*& j < pad ==> v[j] == c) &*&
            (forall int j; pad <= j &*& j < i ==> v[j] == s[j - pad]);
        @*/
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