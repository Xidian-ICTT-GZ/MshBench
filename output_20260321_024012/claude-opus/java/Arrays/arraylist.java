class ArrayList {
    byte[] elems;
    short count;
    
    /*@
    predicate arraylist(ArrayList this;) =
        this.elems |-> ?elems &*& elems.length |-> ?len &*& this.count |-> ?count;
    @*/

    //@ requires size >= 0;
    //@ ensures elems.length == size &*& count == 0;
    ArrayList(short size)
    {
        elems = new byte[size];
        count = 0;
    }
    
    //@ requires true;
    //@ ensures true;
    short getCount()
    {
        return count;
    }
    
    //@ requires 0 <= index && index < elems.length;
    //@ ensures true;
    byte get(short index)
    {
        return elems[index];
    }
    
    //@ requires true;
    //@ ensures 0 <= count && count <= elems.length;
    //@ ensures (result == false ==> count == old(count)) && (result == true ==> count == old(count) + 1);
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