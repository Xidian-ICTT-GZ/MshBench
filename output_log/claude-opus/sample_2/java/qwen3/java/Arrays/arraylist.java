class ArrayList {
    byte[] elems;
    short count;

    //@ requires 0 <= size &*& size <= Short.MAX_VALUE;
    //@ ensures elems == result.elems &*& count == result.count &*&
    //           length(result.elems) == size &*&
    //           0 <= result.count &*& result.count <= size;
    ArrayList(short size)
    {
        elems = new byte[size];
    }

    //@ requires true;
    //@ ensures result == count;
    short getCount()
    {
        return count;
    }

    //@ requires 0 <= index &*& index < length(elems);
    //@ ensures result == elems[index];
    byte get(short index)
    {
        return elems[index];
    }

    //@ requires 0 <= count &*& count <= length(elems);
    //@ ensures (count < length(elems) ==> result == true &*&
    //           elems[count] == value &*& count' == count + 1) &*&
    //          (count == length(elems) ==> result == false &*& count' == count);
    boolean add(byte value)
    {
        if (count == elems.length)
            return false;
        elems[count++] = value;
        return true;
    }
}

/*@ predicate array_list(ArrayList l; short size, short cnt, byte* data) =
    l.elems |-> ?a &*&
    array_block(a, size) &*&
    l.count |-> cnt &*&
    0 <= cnt &*& cnt <= size &*&
    length(a) == size &*&
    cnt == length(data) &*&
    array_slice(a, 0, cnt, data) &*&
    array_slice(a, cnt, size - cnt, _);
@*/

/*@ lemma void array_list_add_success(ArrayList l; short size, short cnt, byte val)
    requires array_list(l; size, cnt, ?data) &*& cnt < size;
    ensures array_list(l; size, cnt + 1, ?data') &*& data'[cnt] == val;
{
    open array_list(l; size, cnt, data);
    assert l.elems |-> ?a &*& array_block(a, size) &*& l.count |-> cnt;
    a[cnt] = val;
    close array_list(l; size, cnt + 1, data);
}
@*/

/*@ lemma void array_list_add_fail(ArrayList l; short size, short cnt)
    requires array_list(l; size, cnt, ?data) &*& cnt == size;
    ensures array_list(l; size, cnt, data);
{
    open array_list(l; size, cnt, data);
    close array_list(l; size, cnt, data);
}
@*/

class Program {
    //@ requires true;
    //@ ensures true;
    static void test()
    {
        ArrayList list = new ArrayList((short) 10);
        //@ close array_list(list; 10, 0, ?data);
        if (list.add((byte) 1) && list.add((byte) 2) && list.add((byte) 3)) {
            //@ open array_list(list; 10, 3, ?data);
            short count = list.getCount();
            //@ assert count == 3;
            assert count == 3;
            list.get((short) 2);
        }
    }
}