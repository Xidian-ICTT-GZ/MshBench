/*@
predicate ArrayList(ArrayList list; byte[] elems, short count) =
    list.elems |-> elems &*& list.count |-> count &*&
    elems != null &*& array_slice(elems, 0, elems.length, _) &*&
    0 <= count &*& count <= elems.length;
@*/

class ArrayList {
    byte[] elems;
    short count;
    
    ArrayList(short size)
        //@ requires 0 <= size;
        //@ ensures ArrayList(this, _, 0);
    {
        elems = new byte[size];
        //@ close ArrayList(this, elems, (short)0);
    }
    
    short getCount()
        //@ requires ArrayList(this, ?elems, ?count);
        //@ ensures ArrayList(this, elems, count) &*& result == count;
    {
        //@ open ArrayList(this, elems, count);
        short c = count;
        //@ close ArrayList(this, elems, count);
        return c;
    }
    
    byte get(short index)
        //@ requires ArrayList(this, ?elems, ?count) &*& 0 <= index &*& index < count;
        //@ ensures ArrayList(this, elems, count);
    {
        //@ open ArrayList(this, elems, count);
        byte v = elems[index];
        //@ close ArrayList(this, elems, count);
        return v;
    }
    
    boolean add(byte value)
        //@ requires ArrayList(this, ?elems, ?count);
        //@ ensures result ? ArrayList(this, elems, (short)(count + 1)) : ArrayList(this, elems, count);
    {
        //@ open ArrayList(this, elems, count);
        if (count == elems.length) {
            //@ close ArrayList(this, elems, count);
            return false;
        }
        elems[count++] = value;
        //@ close ArrayList(this, elems, (short)(count));
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