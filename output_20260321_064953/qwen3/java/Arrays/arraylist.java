class ArrayList {
    byte[] elems;
    short count;
    
    /*@
    predicate valid() = 
        elems != null &*& 
        0 <= count &*& count <= elems.length;
    @*/
    
    //@ requires true;
    //@ ensures valid();
    ArrayList(short size)
    {
        elems = new byte[size];
        //@ close valid();
    }
    
    //@ requires valid();
    //@ ensures result == count;
    short getCount()
    {
        return count;
    }
    
    //@ requires valid() &*& 0 <= index &*& index < count;
    //@ ensures result == elems[index];
    byte get(short index)
    {
        return elems[index];
    }
    
    //@ requires valid();
    //@ ensures valid() &*& result == (old(count) < old(elems.length));
    boolean add(byte value)
    {
        if (count == elems.length)
            return false;
        //@ open valid();
        elems[count++] = value;
        //@ close valid();
        return true;
    }
}

class Program {
    static void test()
    {
        ArrayList list = new ArrayList((short)10);
        //@ open list.valid();
        if (list.add((byte)1) && list.add((byte)2) && list.add((byte)3)) {
            short count = list.getCount();
            //@ assert count == 3;
            list.get((short)2);
        }
        //@ close list.valid();
    }
}