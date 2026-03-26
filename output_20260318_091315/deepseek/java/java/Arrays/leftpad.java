public class LeftPad {

    //@ predicate char_array(char[] cs, int n) = cs != null &*& cs.length == n &*& array_slice(cs, 0, n, _);
    //@ predicate char_array_full(char[] cs) = char_array(cs, cs.length);

    //@ requires s != null;
    //@ requires n >= 0;
    //@ requires s.length <= Integer.MAX_VALUE - n;
    //@ ensures result != null;
    //@ ensures result.length == Math.max(n, s.length);
    static char[] leftPad(char c, int n, char[] s)
    {
        //@ close char_array(s, s.length);
        int pad = Math.max(n - s.length, 0);
        //@ assert pad >= 0;
        //@ assert pad == n - s.length ? n >= s.length : pad == 0;
        //@ int total_len = pad + s.length;
        //@ assert total_len >= 0;
        //@ assert total_len == Math.max(n, s.length);
        //@ assume total_len <= Integer.MAX_VALUE);
        char[] v = new char[pad + s.length];
        //@ close char_array(v, v.length);
        int i = 0;
        //@ close char_array(v, v.length);
        //@ close [f]char_array(s, s.length);

        //@ loop_invariant 0 <= i &*& i <= pad;
        //@ loop_invariant char_array(v, v.length) &*& [f]char_array(s, s.length);
        //@ loop_invariant array_slice_char(v, 0, i, _);
        //@ loop_invariant i == pad ? true : array_slice_char(v, i, pad, _);
        for(; ; i++)
        {
            //@ open char_array(v, v.length);
            if (i == pad) {
                //@ close char_array(v, v.length);
                break;
            }
            //@ array_slice_split(v, i, i+1);
            v[i] = c;
            //@ array_slice_merge(v, i);
            //@ close char_array(v, v.length);
        }
        //@ assert i == pad;
        //@ open char_array(v, v.length);
        
        //@ loop_invariant pad <= i &*& i <= v.length;
        //@ loop_invariant char_array(v, v.length) &*& [f]char_array(s, s.length);
        //@ loop_invariant array_slice_char(v, 0, pad, _);
        //@ loop_invariant array_slice_char(v, pad, i, _);
        //@ loop_invariant i == v.length ? true : array_slice_char(v, i, v.length, _);
        for(; ; i++)
        {
            //@ open char_array(v, v.length);
            if (i == v.length) {
                //@ close char_array(v, v.length);
                break;
            }
            //@ array_slice_split(v, i, i+1);
            //@ open [f]char_array(s, s.length);
            //@ array_slice_split(s, i - pad, i - pad + 1);
            v[i] = s[i - pad];
            //@ array_slice_merge(s, i - pad);
            //@ close [f]char_array(s, s.length);
            //@ array_slice_merge(v, i);
            //@ close char_array(v, v.length);
        }
        //@ assert i == v.length;
        //@ open char_array(v, v.length);
        //@ open [f]char_array(s, s.length);
        //@ close char_array_full(v);
        return v;
    }
    
}