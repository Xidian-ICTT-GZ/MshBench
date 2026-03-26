class ArrayList {
    byte[] elems;
    short count;
    
    /*@
    predicate arraylist() = 
        elems |-> ?elems0 &*&
        count |-> ?count0 &*&
        elems0 != null &*&
        0 <= count0 &*& count0 <= elems0.length;
    @*/
    
    //@ requires 0 <= size;
    //@ ensures arraylist();
    ArrayList(short size)
    {
        elems = new byte[size];
        count = 0;
    }
    
    //@ requires arraylist();
    //@ ensures arraylist() &*& result == count;
    short getCount()
    {
        return count;
    }
    
    //@ requires arraylist() &*& 0 <= index &*& index < count;
    //@ ensures arraylist() &*& result == elems[index];
    byte get(short index)
    {
        return elems[index];
    }
    
    //@ requires arraylist();
    //@ ensures arraylist() &*& (result ? count == old(count) + 1 : count == old(count));
    boolean add(byte value)
    {
        //@ open arraylist();
        if (count == elems.length) {
            //@ close arraylist();
            return false;
        }
        elems[count++] = value;
        //@ close arraylist();
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