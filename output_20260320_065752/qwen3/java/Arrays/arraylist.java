class ArrayList {
    byte[] elems;
    short count;
    
    /*@
    predicate ArrayList(ArrayList a; byte[] es, short c) =
        a.elems |-> es &*& a.count |-> c &*& 0 <= c &*& c <= es.length;
    @*/

    //@ requires size >= 0;
    //@ ensures ArrayList(this, result_, count_) &*& count_ == 0;
    ArrayList(short size)
    {
        elems = new byte[size];
        //@ close ArrayList(this, elems, (short)0);
    }
    
    //@ requires ArrayList(this, ?es, ?c);
    //@ ensures ArrayList(this, es, c) &*& result == c;
    short getCount()
    {
        return count;
    }
    
    //@ requires ArrayList(this, ?es, ?c) &*& 0 <= index &*& index < c;
    //@ ensures ArrayList(this, es, c) &*& result == es[index];
    byte get(short index)
    {
        return elems[index];
    }
    
    //@ requires ArrayList(this, ?es, ?c) &*& c <= es.length;
    //@ ensures ArrayList(this, es, c + (result ? 1 : 0)) &*& c + (result ? 1 : 0) <= es.length;
    boolean add(byte value)
    {
        if (count == elems.length)
            return false;
        //@ open ArrayList(this, es, c);
        elems[count++] = value;
        //@ close ArrayList(this, es, (short)(c + 1));
        return true;
    }
}

class Program {
    //@ requires true;
    //@ ensures true;
    static void test()
    {
        ArrayList list = new ArrayList((short)10);
        //@ open ArrayList(list, _, _);
        if (list.add((byte)1) && list.add((byte)2) && list.add((byte)3)) {
            //@ open ArrayList(list, ?es, ?c);
            short count = list.getCount();
            //@ assert c == 3;
            //@ close ArrayList(list, es, c);
            list.get((short)2);
        }
    }
}