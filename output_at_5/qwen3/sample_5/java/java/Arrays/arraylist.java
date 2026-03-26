class ArrayList {
    byte[] elems;
    short count;

    /*@
    predicate arrayBytes(byte[] arr, int len) = true;
    @*/

    ArrayList(short size)
        //@ requires true;
        //@ ensures arrayBytes(elems, size) &*& count == 0;
    {
        elems = new byte[size];
    }

    short getCount()
        //@ requires true;
        //@ ensures result == count;
    {
        return count;
    }

    byte get(short index)
        //@ requires 0 <= (int)index &*& (int)index < count;
        //@ ensures true;
    {
        return elems[index];
    }

    boolean add(byte value)
        //@ requires true;
        //@ ensures result ==> count == old(count) + 1 &*& arrayBytes(elems, elems.length);
        //@ ensures !result ==> count == old(count) &*& arrayBytes(elems, elems.length);
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
        ArrayList list = new ArrayList((short)10);
        if (list.add((byte)1) && list.add((byte)2) && list.add((byte)3)) {
            short count = list.getCount();
            assert count == 3;
            list.get((short)2);
        }
    }
}