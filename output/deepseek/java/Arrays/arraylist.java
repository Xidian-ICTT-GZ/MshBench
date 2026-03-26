class ArrayList {
    byte[] elems;
    short count;

    //@ predicate valid(short size) = elems |-> ?a &*& a != null &*& a.length == size &*& array_slice(a, 0, size, _) &*& count |-> 0 &*& size >= 0;
    //@ predicate valid() = elems |-> ?a &*& a != null &*& array_slice(a, 0, a.length, _) &*& count |-> ?c &*& 0 <= c &*& c <= a.length;

    ArrayList(short size)
    //@ requires size >= 0;
    //@ ensures valid(size);
    {
        elems = new byte[size];
    }

    short getCount()
    //@ requires valid();
    //@ ensures valid() &*& result == count;
    {
        return count;
    }

    byte get(short index)
    //@ requires valid() &*& 0 <= index &*& index < count;
    //@ ensures valid();
    {
        return elems[index];
    }

    boolean add(byte value)
    //@ requires valid();
    //@ ensures valid() &*& (result ? true : count == old(count) &*& count == elems.length);
    {
        if (count == elems.length)
            return false;
        elems[count++] = value;
        return true;
    }
}

class Program {
    static void test()
    //@ requires true;
    //@ ensures true;
    {
        ArrayList list = new ArrayList((short) 10);
        //@ list.valid(10);
        //@ list.valid();
        if (list.add((byte) 1) && list.add((byte) 2) && list.add((byte) 3)) {
            short count = list.getCount();
            //@ assert count == 3;
            list.get((short) 2);
        }
    }
}