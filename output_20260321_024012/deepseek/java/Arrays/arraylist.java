class ArrayList {
    byte[] elems;
    short count;
    
    /*@
    predicate valid() =
        elems |-> ?a
        &*& a != null
        &*& count |-> ?c
        &*& 0 <= c && c <= a.length;
    @*/
    
    //@ requires 0 <= size;
    //@ ensures valid();
    ArrayList(short size)
    {
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
    
    //@ requires valid() &*& 0 <= index && index < count;
    //@ ensures valid();
    byte get(short index)
    {
        //@ open valid();
        return elems[index];
        //@ close valid();
    }
    
    //@ requires valid();
    //@ ensures valid() &*& (result ? true : true);
    boolean add(byte value)
    {
        //@ open valid();
        if (count == elems.length)
            //@ close valid();
            return false;
        elems[count++] = value;
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