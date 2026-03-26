class ArrayList {
    byte[] elems;
    short count;
    
    





        
    ArrayList(short size)
        
        
    {
        elems = new byte[size];
    }
    
    short getCount()
        
        
    {
        return count;
    }
    
    byte get(short index)
        
        
    {
        return elems[index];
    }
    
    boolean add(byte value)
        
        
    {
        if (count == elems.length)
            return false;
        elems[count++] = value;
        return true;
    }
}

class Program {
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