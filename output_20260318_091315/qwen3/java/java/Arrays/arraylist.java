/*@ predicate ArrayList(ArrayList a; byte[] elems, short count) =
    a.elems |-> elems &*& a.count |-> count &*&
    0 <= count &*& count <= elems.length &*&
    chars(elems, ?cs) &*&
    foreach(cs, (c) => true);
@*/

class ArrayList {
    byte[] elems;
    short count;

    //@ requires 0 <= size &*& size <= 32767;
    //@ ensures ArrayList(result, ?elems, (short)0) &*& elems.length == size;
    ArrayList(short size)
    {
        elems = new byte[size];
        //@ close ArrayList(this, elems, (short)0);
    }

    //@ requires ArrayList(this, ?elems, ?count);
    //@ ensures ArrayList(this, elems, count) &*& result == count;
    short getCount()
    {
        return count;
    }

    //@ requires ArrayList(this, ?elems, ?count) &*& 0 <= index &*& index < count;
    //@ ensures ArrayList(this, elems, count) &*& result == elems[index];
    byte get(short index)
    {
        return elems[index];
    }

    //@ requires ArrayList(this, ?elems, ?count) &*& count < elems.length;
    //@ ensures ArrayList(this, elems, ?newCount) &*&
    
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
        ArrayList list = new ArrayList((short)10);
        if (list.add((byte)1) && list.add((byte)2) && list.add((byte)3)) {
            short count = list.getCount();
            assert count == 3;
            list.get((short)2);
        }
    }
}