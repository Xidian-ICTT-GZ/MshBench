public class LeftPad {

    //@ predicate charArray(char[] cs; int n, list<char> vs) = cs != null &*& cs.length |-> n &*& array_slice(cs, 0, n, vs);
    //@ predicate charArrayFull(char[] cs; list<char> vs) = charArray(cs, ?n, vs) &*& n == length(vs);

    /*@
    requires n >= 0;
    ensures charArrayFull(result, ?vs) &*& length(vs) == n;
    @*/
    static char[] createCharArray(int n)
    //@ requires n >= 0;
    //@ ensures charArrayFull(result, ?vs) &*& length(vs) == n;
    {
        return new char[n];
    }

    /*@
    requires charArrayFull(s, ?s_vals);
    ensures charArrayFull(result, ?v_vals) &*& length(v_vals) == Math.max(n - length(s_vals), 0) + length(s_vals);
    @*/
    static char[] leftPad(char c, int n, char[] s)
    //@ requires charArrayFull(s, ?s_vals);
    //@ ensures charArrayFull(result, ?v_vals) &*& length(v_vals) == Math.max(n - length(s_vals), 0) + length(s_vals);
    {
        int pad = Math.max(n - s.length, 0);
        //@ assert pad >= 0;
        char[] v = new char[pad + s.length];
        //@ close charArray(v, pad + s.length, _);
        //@ close charArrayFull(v, ?v_vals_init);
        //@ assert length(v_vals_init) == pad + s.length;
        int i = 0;

        //@ loop_invariant 0 <= i &*& i <= pad;
        //@ loop_invariant charArrayFull(v, ?v_vals_loop) &*& length(v_vals_loop) == pad + s.length;
        //@ loop_invariant array_slice_char(v, 0, i, ?prefix) &*& all_eq(prefix, c) == true;
        //@ loop_invariant array_slice_char(v, i, pad + s.length, ?suffix_loop);
        for(; ; i++)
        //@ requires 0 <= i &*& i <= pad;
        //@ requires charArrayFull(v, ?v_vals_loop) &*& length(v_vals_loop) == pad + s.length;
        //@ requires array_slice_char(v, 0, i, ?prefix) &*& all_eq(prefix, c) == true;
        //@ requires array_slice_char(v, i, pad + s.length, ?suffix_loop);
        //@ ensures i == pad;
        //@ ensures charArrayFull(v, ?v_vals_loop2) &*& length(v_vals_loop2) == pad + s.length;
        //@ ensures array_slice_char(v, 0, pad, ?prefix2) &*& all_eq(prefix2, c) == true;
        //@ ensures array_slice_char(v, pad, pad + s.length, suffix_loop);
        {
            //@ open charArrayFull(v, _);
            //@ open charArray(v, _, _);
            if (i == pad) {
                //@ close charArray(v, pad + s.length, _);
                //@ close charArrayFull(v, _);
                break;
            }
            //@ array_slice_split(v, i, i+1);
            v[i] = c;
            //@ array_slice_merge(v, 0, i, i+1);
            //@ close charArray(v, pad + s.length, _);
            //@ close charArrayFull(v, _);
        }
        //@ assert i == pad;
        //@ assert array_slice_char(v, 0, pad, ?prefix_final) &*& all_eq(prefix_final, c) == true;
        //@ assert array_slice_char(v, pad, pad + s.length, ?middle);

        //@ loop_invariant pad <= i &*& i <= pad + s.length;
        //@ loop_invariant charArrayFull(v, ?v_vals_loop2) &*& length(v_vals_loop2) == pad + s.length;
        //@ loop_invariant array_slice_char(v, 0, pad, prefix_final) &*& all_eq(prefix_final, c) == true;
        //@ loop_invariant array_slice_char(v, pad, i, ?copied) &*& array_slice_char(s, 0, i - pad, copied);
        //@ loop_invariant array_slice_char(v, i, pad + s.length, ?rest);
        for(; ; i++)
        //@ requires pad <= i &*& i <= pad + s.length;
        //@ requires charArrayFull(v, ?v_vals_loop2) &*& length(v_vals_loop2) == pad + s.length;
        //@ requires array_slice_char(v, 0, pad, prefix_final) &*& all_eq(prefix_final, c) == true;
        //@ requires array_slice_char(v, pad, i, ?copied) &*& array_slice_char(s, 0, i - pad, copied);
        //@ requires array_slice_char(v, i, pad + s.length, ?rest);
        //@ ensures i == pad + s.length;
        //@ ensures charArrayFull(v, ?v_vals_final) &*& length(v_vals_final) == pad + s.length;
        //@ ensures array_slice_char(v, 0, pad, prefix_final) &*& all_eq(prefix_final, c) == true;
        //@ ensures array_slice_char(v, pad, pad + s.length, ?all_copied) &*& array_slice_char(s, 0, s.length, all_copied);
        {
            //@ open charArrayFull(v, _);
            //@ open charArray(v, _, _);
            if (i == v.length) {
                //@ close charArray(v, pad + s.length, _);
                //@ close charArrayFull(v, _);
                break;
            }
            //@ array_slice_split(v, i, i+1);
            v[i] = s[i - pad];
            //@ array_slice_merge(v, pad, i, i+1);
            //@ close charArray(v, pad + s.length, _);
            //@ close charArrayFull(v, _);
        }
        //@ close charArrayFull(v, _);
        return v;
    }

}