class ArrayList {
    byte[] elems;
    short count;
    
    //@ predicate valid() = elems |-> ?a &*& a != null &*& array_slice(a, 0, a.length, _) &*& count |-> ?c &*& 0 <= c &*& c <= a.length;
    
    //@ requires 0 <= size &*& size <= 32767;
    //@ ensures valid();
    ArrayList(short size)
    {
        //@ close array_slice(new byte[size], 0, size, _);
        elems = new byte[size];
        //@ close valid();
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
        //@ array_slice_store(elems, count);
        elems[count] = value;
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
        boolean b1 = list.add((byte)1);
        boolean b2 = list.add((byte)2);
        boolean b3 = list.add((byte)3);
        if (b1 && b2 && b3) {
            short count = list.getCount();
            //@ assert count == 3;
            list.get((short)2);
        }
    }
}