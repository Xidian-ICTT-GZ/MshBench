class ArrayList {
    byte[] elems;
    short count;

    //@ predicate valid() = elems |-> ?e &*& count |-> ?c &*& 0 <= c &*& c <= e.length;

    //@ requires elems |-> _;
    //@ ensures valid();
    ArrayList(short size)
    {
        elems = new byte[size];
    }

    //@ requires valid();
    //@ ensures valid() &*& result == count;
    short getCount()
    {
        return count;
    }

    //@ requires valid() &*& 0 <= index &*& index < count;
    //@ ensures valid() &*& result == elems[index];
    byte get(short index)
    {
        return elems[index];
    }

    //@ requires valid();
    //@ ensures valid();
    boolean add(byte value)
    {
        if (count == elems.length)
            return false;
        elems[count++] = value;
        return true;
    }
}

class Program {
    //@ requires true;
    //@ ensures true;
    static void test()
    {
        ArrayList list = new ArrayList((short) 10);
        if (list.add((byte) 1) && list.add((byte) 2) && list.add((byte) 3)) {
            short count = list.getCount();
            assert count == 3;
            list.get((short) 2);
        }
    }
}