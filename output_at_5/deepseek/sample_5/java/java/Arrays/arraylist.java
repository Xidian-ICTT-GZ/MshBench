class ArrayList {
    byte[] elems;
    short count;
    
    /*@
    predicate valid() = 
        elems |-> ?e 
        &*& count |-> ?c 
        &*& e != null 
        &*& 0 <= c 
        &*& c <= e.length 
        &*& array_slice(e, 0, c, _) 
        &*& array_slice(e, c, e.length, _);
    @*/
    
    ArrayList(short size)
    //@ requires 0 <= size;
    //@ ensures valid();
    {
        elems = new byte[size];
        count = 0;
        //@ close valid();
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
        //@ assert list.valid();
        boolean b1 = list.add((byte)1);
        //@ assert list.valid();
        boolean b2 = list.add((byte)2);
        //@ assert list.valid();
        boolean b3 = list.add((byte)3);
        if (b1 && b2 && b3) {
            short count = list.getCount();
            //@ assert count == 3;
            list.get((short)2);
        }
    }
}