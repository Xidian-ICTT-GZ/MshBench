/*@
predicate ArrayListInv(ArrayList list, byte[] e, short c) =
    list.elems |-> e &*& list.count |-> c &*& e != null &*& array_slice(e, 0, e.length, _) &*& 0 <= c &*& c <= e.length;
@*/

class ArrayList {
    byte[] elems;
    short count;

    //@ requires size > 0;
    //@ ensures ArrayListInv(this, ?e, 0) &*& e.length == size;
    ArrayList(short size)
    {
        elems = new byte[size];
        //@ close ArrayListInv(this, elems, (short)0);
    }

    //@ requires ArrayListInv(this, ?e, ?c);
    //@ ensures ArrayListInv(this, e, c) &*& result == c;
    short getCount()
    {
        //@ open ArrayListInv(this, e, c);
        short r = count;
        //@ close ArrayListInv(this, elems, count);
        return r;
    }

    //@ requires ArrayListInv(this, ?e, ?c) &*& 0 <= index &*& index < c;
    //@ ensures ArrayListInv(this, e, c);
    byte get(short index)
    {
        //@ open ArrayListInv(this, e, c);
        byte r = elems[index];
        //@ close ArrayListInv(this, elems, count);
        return r;
    }

    //@ requires ArrayListInv(this, ?e, ?c);
    //@ ensures result == true &*& ArrayListInv(this, e, (short)(c + 1)) &*& c < e.length || result == false &*& ArrayListInv(this, e, c) &*& c == e.length;
    boolean add(byte value)
    {
        //@ open ArrayListInv(this, e, c);
        if (count == elems.length) {
            //@ close ArrayListInv(this, elems, count);
            return false;
        }
        elems[count++] = value;
        //@ close ArrayListInv(this, elems, count);
        return true;
    }
}

class Program {
    //@ requires true;
    //@ ensures true;
    static void test()
    {
        ArrayList list = new ArrayList((short) 10);
        if (list.add((byte) 1) && list.add((byte) 2) && list.add((byte) 3)) {
            short count = list.getCount();
            assert count == 3;
            list.get((short) 2);
        }
    }
}