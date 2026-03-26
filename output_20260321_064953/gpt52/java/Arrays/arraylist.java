class ArrayList {
    byte[] elems;
    short count;
    
    /*@
    predicate valid() =
        this.elems |-> ?es &*& this.count |-> ?c &*& es != null;
    @*/
    
    

        
    ArrayList(short size)
        
        
    //@ requires size >= 0;
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
        short result = count;
        //@ close valid();
        return result;
    }
    
    byte get(short index)
        
        
    //@ requires valid();
    //@ ensures valid();
    {
        //@ open valid();
        //@ close valid();
        return elems[index];
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
        if (list.add((byte)1) && list.add((byte)2) && list.add((byte)3)) {
            short count = list.getCount();
            assert count == 3;
            list.get((short)2);
        }
    }
}