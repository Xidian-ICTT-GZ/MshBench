class ArrayList {
    byte[] elems;
    short count;
    
    /*@
    predicate valid() =
        this.elems |-> ?a &*& this.count |-> ?c &*& a != null &*& 0 <= c &*& c <= a.length;
    @*/
    
    

        
    ArrayList(short size)
        
        
    //@ requires 0 <= size;
    //@ ensures valid();
    {
        elems = new byte[size];
        //@ close valid();
    }
    
    short getCount()
        
        
    //@ requires valid();
    //@ ensures valid() &*& result == count;
    {
        //@ open valid();
        short r = count;
        //@ close valid();
        return r;
    }
    
    byte get(short index)
        
        
    //@ requires valid() &*& 0 <= index &*& index < count;
    //@ ensures valid();
    {
        //@ open valid();
        byte r = elems[index];
        //@ close valid();
        return r;
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
        elems[count++] = value;
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
        if (list.add((byte)1) && list.add((byte)2) && list.add((byte)3)) {
            short count = list.getCount();
            assert count == 3;
            list.get((short)2);
        }
    }
}