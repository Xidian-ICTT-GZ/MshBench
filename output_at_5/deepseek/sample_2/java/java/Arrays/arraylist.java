class ArrayList {
    byte[] elems;
    short count;
    
    //@ predicate valid() = elems |-> ?e &*& count |-> ?c &*& e != null &*& 0 <= c &*& c <= e.length &*& array_slice(e, 0, c, _) &*& array_slice(e, c, e.length, _);
    
    ArrayList(short size)
    //@ requires 0 <= size;
    //@ ensures valid();
    {
        //@ close valid();
        elems = new byte[size];
        //@ close array_slice(elems, 0, size, _);
    }
    
    short getCount()
    //@ requires valid();
    //@ ensures valid() &*& result == count;
    {
        //@ open valid();
        short result = count;
        //@ close valid();
        return result;
    }
    
    byte get(short index)
    //@ requires valid() &*& 0 <= index &*& index < count;
    //@ ensures valid();
    {
        //@ open valid();
        byte result = elems[index];
        //@ close valid();
        return result;
    }
    
    boolean add(byte value)
    //@ requires valid();
    //@ ensures valid();
    {
        //@ open valid();
        if (count == elems.length) {
            //@ close valid();
            return false;
        }
        elems[count] = value;
        count = (short)(count + 1);
        //@ close valid();
        return true;
    }
}

class Program {
    static void test()
    //@ requires true;
    //@ ensures true;
    {
        ArrayList list = new ArrayList((short)10);
        //@ open list.valid();
        //@ close list.valid();
        if (list.add((byte)1) && list.add((byte)2) && list.add((byte)3)) {
            short count = list.getCount();
            //@ assert count == 3;
            list.get((short)2);
        }
    }
}