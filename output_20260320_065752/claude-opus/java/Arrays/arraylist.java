class ArrayList {
    byte[] elems;
    short count;
    
    /*@
    predicate array_list(ArrayList this) =
        this.elems |-> ?elems &*& elems.length |-> ?len &*&
        0 <= this.count &*& this.count <= len &*&
        pointer(this.elems, _) &*& this.count |-> _; // abstract ownership
    @*/

    //@ requires size >= 0;
    //@ ensures true;
    ArrayList(short size)
    {
        //@ open true;
        elems = new byte[size];
        //@ close true;
    }
    
    //@ requires true;
    //@ ensures true;
    short getCount()
    {
        return count;
    }
    
    //@ requires elems != null &*& 0 <= index &*& index < elems.length;
    //@ ensures true;
    byte get(short index)
    {
        return elems[index];
    }
    
    //@ requires elems != null &*& 0 <= count &*& count < elems.length;
    //@ ensures true;
    boolean add(byte value)
    {
        if (count == elems.length)
            return false;
        elems[count++] = value;
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