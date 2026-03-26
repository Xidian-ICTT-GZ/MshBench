class ArrayList {
    byte[] elems;
    short count;

    /*@
    predicate valid(int c) =
        this.elems |-> ?arr &*& this.count |-> c &*&
        arr != null &*& array_slice(arr, 0, arr.length, _) &*&
        c >= 0 &*& c <= arr.length &*& arr.length <= 32767;
    @*/

    //@ requires size >= 0 &*& size <= 32767;
    //@ ensures valid(0);
    ArrayList(short size)

    {
        elems = new byte[size];
        //@ close valid(0);
    }

    //@ requires valid(?c);
    //@ ensures valid(c) &*& result == c;
    short getCount()

    {
        //@ open valid(c);
        //@ close valid(c);
        return count;
    }

    //@ requires valid(?c) &*& index >= 0 &*& index < c;
    //@ ensures valid(c);
    byte get(short index)

    {
        //@ open valid(c);
        //@ close valid(c);
        return elems[index];
    }

    //@ requires valid(?c);
    //@ ensures (c < elems.length &*& valid(c + 1) &*& result == true) || (c == elems.length &*& valid(c) &*& result == false);
    boolean add(byte value)

    {
        //@ open valid(c);
        if (count == elems.length) {
            //@ close valid(c);
            return false;
        }
        elems[count++] = value;
        //@ close valid(c + 1);
        return true;
    }
}

class Program {
    //@ requires true;
    //@ ensures true;
    static void test()

    {
        ArrayList list = new ArrayList((short) 10);
        //@ open list.valid(0);
        //@ close list.valid(0);
        if (list.add((byte) 1) && list.add((byte) 2) && list.add((byte) 3)) {
            short count = list.getCount();
            //@ assert list.valid(3);
            list.get((short) 2);
        }
    }
}