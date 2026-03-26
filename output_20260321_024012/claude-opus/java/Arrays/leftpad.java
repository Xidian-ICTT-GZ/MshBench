public class LeftPad {

    //@ requires s != null;
    //@ ensures result != null &*& result.length == Math.max(n - s.length, 0) + s.length;
    static char[] leftPad(char c, int n, char[] s)
    {
        int pad = Math.max(n - s.length, 0);
        char[] v = new char[pad + s.length];
        int i = 0;

        //@ // loop to set left padding characters
        for(; ; i++)
        {
            if (i == pad) {
                break;
            }

            v[i] = c;
        }

        //@ // loop to copy original characters after padding
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