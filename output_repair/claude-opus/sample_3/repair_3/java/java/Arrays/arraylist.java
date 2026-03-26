class ArrayList {
    byte[] elems;
    short count;

    /*@ predicate valid() = elems |-> ?e &*& count |-> ?c &*& 0 <= c &*& c <= e.length; @*/

    ArrayList(short size)
    //@ requires 0 <= size;
    //@ ensures elems |-> _ &*& count |-> 0;
    {
        elems = new byte[size];
    }

    short getCount()
    //@ requires this.valid();
    //@ ensures this.valid() &*& result == count;
    {
        return count;
    }

    byte get(short index)
    //@ requires this.valid();
    //@ ensures this.valid();
    {
        return elems[index];
    }

    boolean add(byte value)
    //@ requires this.valid();
    //@ ensures this.valid();
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
        if (list.add((byte) 1) && list.add((byte) 2) && list.add((byte) 3)) {
            short count = list.getCount();
            assert count == 3;
            list.get((short) 2);
        }
    }
}