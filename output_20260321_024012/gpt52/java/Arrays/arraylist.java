class ArrayList {
    byte[] elems;
    short count;
    
    /*@
    predicate ArrayListInv() =
        this.elems |-> ?es &*& this.count |-> ?c;
    @*/
    

        
    ArrayList(short size)
        
        
    //@ requires true;
    //@ ensures ArrayListInv();
    {
        //@ close ArrayListInv();
        //@ open ArrayListInv();
        elems = new byte[size];
        //@ close ArrayListInv();
    }
    
    short getCount()
        
        
    //@ requires ArrayListInv();
    //@ ensures ArrayListInv() &*& result == count;
    {
        //@ open ArrayListInv();
        short r = count;
        //@ close ArrayListInv();
        return r;
    }
    
    byte get(short index)
        
        
    //@ requires ArrayListInv();
    //@ ensures ArrayListInv();
    {
        //@ open ArrayListInv();
        byte r = elems[index];
        //@ close ArrayListInv();
        return r;
    }
    
    boolean add(byte value)
        
        
    //@ requires ArrayListInv();
    //@ ensures ArrayListInv();
    {
        //@ open ArrayListInv();
        if (count == elems.length) {
            //@ close ArrayListInv();
            return false;
        }
        elems[count++] = value;
        //@ close ArrayListInv();
        return true;
    }
}

class Program {
    static void test()
        
        
    //@ requires true;
    //@ ensures true;
    {
        ArrayList list = new ArrayList((short)10);
        //@ open list.ArrayListInv();
        //@ close list.ArrayListInv();
        if (list.add((byte)1) && list.add((byte)2) && list.add((byte)3)) {
            short count = list.getCount();
            assert count == 3;
            list.get((short)2);
        }
    }
}