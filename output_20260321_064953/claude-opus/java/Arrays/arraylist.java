class ArrayList {
    byte[] elems;
    short count;
    
    /*@
    predicate arraylist(this) =
        this.elems |-> ?elems &*& elems.length |-> ?len &*&
        this.count |-> ?count;
    @*/
    
    //@ requires size >= 0;
    //@ ensures arraylist(this) &*& elems.length == size &*& count == 0;
    ArrayList(short size)
    {
        elems = new byte[size];
        count = 0;
    }
    
    //@ requires arraylist(this);
    //@ ensures arraylist(this) &*& result == count;
    short getCount()
    {
        return count;
    }
    
    //@ requires arraylist(this) &*& 0 <= index &*& index < elems.length;
    //@ ensures arraylist(this) &*& result == elems[index];
    byte get(short index)
    {
        return elems[index];
    }
    
    //@ requires arraylist(this);
    //@ ensures arraylist(this);
    //@ ensures result ? count == old(count) + 1 : count == old(count);
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