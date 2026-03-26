class ArrayList {
    byte[] elems;
    short count;
    
    /*@ predicate arraylist(ArrayList this, int length, int count) =
          this.elems |-> ?elems_ptr &*&
          array_slice(elems_ptr, length, ?elems_contents) &*&
          this.count |-> count &*&
          0 <= count &*& count <= length;
    @*/
    
    /*@ ensures arraylist(this, size, 0); @*/
    ArrayList(short size)
    {
        elems = new byte[size];
    }
    
    /*@ requires arraylist(this, ?length, ?count); @*/
    /*@ ensures arraylist(this, length, count) &*& result == count; @*/
    short getCount()
    {
        return count;
    }
    
    /*@ requires arraylist(this, ?length, ?count) &*& 0 <= index &*& index < count; @*/
    /*@ ensures arraylist(this, length, count) &*& result == elems[index]; @*/
    byte get(short index)
    {
        return elems[index];
    }
    
    /*@ requires arraylist(this, ?length, ?count) &*& count <= length; @*/
    /*@ ensures
          (count == length
            ==> (arraylist(this, length, count) &*& result == false)) &*&
          (count < length
            ==> (arraylist(this, length, count + 1) &*&
                 elems[count] |-> value &*& result == true));
    @*/
    boolean add(byte value)
    {
        if (count == elems.length)
            return false;
        elems[count++] = value;
        return true;
    }
}

class Program {
    /*@ requires true; @*/
    /*@ ensures true; @*/
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