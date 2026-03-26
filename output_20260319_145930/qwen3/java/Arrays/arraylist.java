/*@ predicate ArrayList(ArrayList list; byte[] elems, short count) =
    list.elems |-> elems &*& list.count |-> count &*&
    0 <= count &*& count <= elems.length &*&
    [_]elems[..] |-> ?_;
@*/

class ArrayList {
    byte[] elems;
    short count;

    //@ requires true;
    //@ ensures ArrayList(this, result, (short)0);
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

    //@ requires ArrayList(this, ?elems, ?count);
    //@ ensures ArrayList(this, elems, count + (result ? 1 : 0)) &*&
    
    boolean add(byte value)
    {
        if (count == elems.length)
            return false;
        //@ open ArrayList(this, elems, count);
        elems[count++] = value;
        //@ close ArrayList(this, elems, count);
        return true;
    }
}

class Program {
    //@ requires true;
    //@ ensures true;
    static void test()
    {
        ArrayList list = new ArrayList((short)10);
        //@ assert ArrayList(list, ?elems, (short)0);
        if (list.add((byte)1) && list.add((byte)2) && list.add((byte)3)) {
            //@ open ArrayList(list, elems, ?count0);
            //@ close ArrayList(list, elems, (short)3);
            short count = list.getCount();
            //@ assert count == 3;
            list.get((short)2);
        }
    }
}