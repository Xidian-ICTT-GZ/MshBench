class ArrayList {
    byte[] elems;
    short count;

    /*@ predicate valid() =
            this.elems |-> ?es
        &*& es != null
        &*& this.count |-> ?c
        &*& 0 <= c
        &*& c <= es.length
        &*& array_slice(es, 0, es.length, _);
    @*/

    ArrayList(short size)
    //@ requires 0 <= size;
    //@ ensures valid();
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
    //@ ensures valid() &*& (result == false || result == true);
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