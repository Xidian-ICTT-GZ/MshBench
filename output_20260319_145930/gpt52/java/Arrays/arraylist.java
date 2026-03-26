/*@

predicate arraylist(ArrayList l; int len, int cnt) =
    l.elems |-> ?a &*& a != null &*& array_slice(a, 0, len, _) &*& l.count |-> (short)cnt &*& 0 <= cnt &*& cnt <= len &*& len == a.length;

@*/

class ArrayList {
    byte[] elems;
    short count;
    
    

        
    ArrayList(short size)
        
        
    //@ requires 0 <= (int)size;
    //@ ensures arraylist(this, (int)size, 0);
    {
        elems = new byte[size];
        //@ close arraylist(this, (int)size, 0);
    }
    
    short getCount()
        
        
    //@ requires arraylist(this, ?len, ?cnt);
    //@ ensures arraylist(this, len, cnt) &*& result == (short)cnt;
    {
        //@ open arraylist(this, ?len, ?cnt);
        short r = count;
        //@ close arraylist(this, len, cnt);
        return r;
    }
    
    byte get(short index)
        
        
    //@ requires arraylist(this, ?len, ?cnt) &*& 0 <= (int)index &*& (int)index < cnt;
    //@ ensures arraylist(this, len, cnt);
    {
        //@ open arraylist(this, ?len, ?cnt);
        byte[] a = elems;
        //@ close arraylist(this, len, cnt);
        return a[index];
    }
    
    boolean add(byte value)
        
        
    //@ requires arraylist(this, ?len, ?cnt);
    //@ ensures arraylist(this, len, cnt + (result ? 1 : 0)) &*& (result ? cnt < len : cnt == len);
    {
        //@ open arraylist(this, ?len, ?cnt);
        byte[] a = elems;
        if (count == elems.length) {
            //@ close arraylist(this, len, cnt);
            return false;
        }
        //@ assert cnt < len;
        a[count++] = value;
        //@ close arraylist(this, len, cnt + 1);
        return true;
    }
}

class Program {
    static void test()
        
        
    //@ requires true;
    //@ ensures true;
    {
        ArrayList list = new ArrayList((short)10);
        //@ open arraylist(list, 10, 0);
        //@ close arraylist(list, 10, 0);
        if (list.add((byte)1) && list.add((byte)2) && list.add((byte)3)) {
            short count = list.getCount();
            assert count == 3;
            list.get((short)2);
        }
    }
}