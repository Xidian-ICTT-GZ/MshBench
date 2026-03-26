class ArrayList {
    byte[] elems;
    short count;
    
    //@ predicate valid() = elems |-> ?a &*& count |-> ?c &*& a != null &*& 0 <= c &*& c <= a.length &*& array_slice(a, 0, c, _) &*& array_slice(a, c, a.length, _);
    
    //@ requires 0 <= size;
    //@ ensures valid();
    ArrayList(short size)
    {
        //@ close array_slice(new byte[size], 0, size, _);
        //@ close valid();
        elems = new byte[size];
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
        //@ open array_slice(elems, count, elems.length, _);
        elems[count] = value;
        //@ close array_slice(elems, count, elems.length, _);
        count++;
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
        //@ open list.valid();
        //@ close list.valid();
        if (list.add((byte)1) && list.add((byte)2) && list.add((byte)3)) {
            short count = list.getCount();
            //@ assert count == 3;
            list.get((short)2);
        }
    }
}