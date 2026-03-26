class ArrayList {
    byte[] elems;
    short count;
    
    //@ predicate valid() = elems |-> ?a &*& a != null &*& array_slice(a, 0, a.length, _) &*& count |-> _ &*& 0 <= count &*& count <= a.length;
    
    //@ requires 0 <= size;
    //@ ensures valid();
    ArrayList(short size)
    {
        //@ close valid();
        elems = new byte[size];
        //@ close array_slice(elems, 0, elems.length, _);
    }
    
    //@ requires valid();
    //@ ensures valid() &*& result == count;
    short getCount()
    {
        //@ open valid();
        return count;
        //@ close valid();
    }
    
    //@ requires valid() &*& 0 <= index &*& index < count;
    //@ ensures valid();
    byte get(short index)
    {
        //@ open valid();
        byte result = elems[index];
        //@ close valid();
        return result;
    }
    
    //@ requires valid();
    //@ ensures valid() &*& (result ? true : true);
    boolean add(byte value)
    {
        //@ open valid();
        if (count == elems.length) {
            //@ close valid();
            return false;
        }
        //@ open array_slice(elems, 0, elems.length, ?vs);
        //@ close array_slice(elems, 0, count, _);
        //@ close array_slice(elems, count, count + 1, _);
        elems[count] = value;
        count = (short)(count + 1);
        //@ close array_slice(elems, 0, count, _);
        //@ close valid();
        return true;
    }
}

class Program {
    //@ requires true;
    //@ ensures true;
    static void test()
    {
        ArrayList list = new ArrayList((short)10);
        //@ assert list.valid();
        if (list.add((byte)1) && list.add((byte)2) && list.add((byte)3)) {
            short count = list.getCount();
            //@ assert count == 3;
            list.get((short)2);
        }
    }
}