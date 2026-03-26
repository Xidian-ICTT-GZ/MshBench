/*@ predicate ArrayList(ArrayList a; int capacity, int size) =
    a.elems |-> ?elems &*&
    a.count |-> ?count &*&
    chars(elems, capacity, _) &*&
    0 <= size &*& size <= capacity &*&
    count == size;
@*/

class ArrayList {
    byte[] elems;
    short count;

    //@ requires 0 <= size &*& size <= Short.MAX_VALUE;
    //@ ensures ArrayList(this, size, 0);
    ArrayList(short size)
    {
        elems = new byte[size];
    }

    //@ requires ArrayList(this, ?capacity, ?size);
    //@ ensures ArrayList(this, capacity, size) &*& result == size;
    short getCount()
    {
        return count;
    }

    //@ requires ArrayList(this, ?capacity, ?size) &*& 0 <= index &*& index < size;
    //@ ensures ArrayList(this, capacity, size) &*& result == elems[index];
    byte get(short index)
    {
        return elems[index];
    }

    //@ requires ArrayList(this, ?capacity, ?size);
    //@ ensures ArrayList(this, capacity, size + (result ? 1 : 0)) &*&
    
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