class ArrayList {
    byte[] elems;
    short count;
    
    /*@
    predicate valid() =
        this.elems |-> ?es &*& this.count |-> ?c &*& es != null &*& array_slice(es, 0, es.length, _);
    @*/
        
    //@ requires true;
    //@ ensures valid();
    ArrayList(short size)
        
        
    {
        elems = new byte[size];
        //@ close valid();
    }
    
    //@ requires valid();
    //@ ensures valid() &*& result == count;
    short getCount()
        
        
    {
        //@ open valid();
        short res = count;
        //@ close valid();
        return res;
    }
    
    //@ requires valid() &*& 0 <= index &*& index < elems.length;
    //@ ensures valid();
    byte get(short index)
        
        
    {
        //@ open valid();
        byte res = elems[index];
        //@ close valid();
        return res;
    }
    
    //@ requires valid();
    //@ ensures valid();
    boolean add(byte value)
        
        
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
    //@ requires true;
    //@ ensures true;
    static void test()
        
        
    {
        ArrayList list = new ArrayList((short)10);
        if (list.add((byte)1) && list.add((byte)2) && list.add((byte)3)) {
            short count = list.getCount();
            assert count == 3;
            list.get((short)2);
        }
    }
}