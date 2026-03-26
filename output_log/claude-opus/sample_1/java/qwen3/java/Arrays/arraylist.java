class ArrayList {
byte[] elems;
short count;

//@ predicate array_list(ArrayList l; short size, short cnt, byte* data) =
//@     l.elems |-> ?a &*&
//@     array_block(a, size) &*&
//@     l.count |-> cnt &*&
//@     0 <= cnt &*& cnt <= size &*&
//@     forall(short i; 0 <= i &*& i < cnt; a[i] == data[i]) &*&
//@     (length(a) == size);

//@ requires 0 <= size &*& size <= Short.MAX_VALUE;
//@ ensures array_list(this; size, 0, nil) &*&
//@         elems == this.elems &*& count == this.count &*& length(elems) == size;
ArrayList(short size)
{
    elems = new byte[size];
    count = 0;
}

//@ requires array_list(this; ?size, ?cnt, ?data) &*& 0 <= index &*& index < size;
//@ ensures array_list(this; size, cnt, data) &*& result == data[index];
byte get(short index)
    requires array_list(this; ?size, ?cnt, ?data) &*& 0 <= index &*& index < cnt;
    ensures array_list(this; size, cnt, data) &*& result == data[index];
{
    return elems[index];
}

//@ requires array_list(this; ?size, ?cnt, ?data) &*& 0 <= cnt &*& cnt <= size;
//@ ensures (cnt < size ==> result == true &*& array_list(this; size, cnt + 1, ?data2) &*& data2[cnt] == value) &*&
//@         (cnt == size ==> result == false &*& array_list(this; size, cnt, data));
boolean add(byte value)
    requires array_list(this; ?size, ?cnt, ?data) &*& cnt <= size;
    ensures (cnt < size ==> result == true &*& array_list(this; size, cnt + 1, ?data2) &*& data2[cnt] == value) &*&
            (cnt == size ==> result == false &*& array_list(this; size, cnt, ?data));
{
    if (count == elems.length)
        return false;
    elems[count++] = value;
    return true;
}

//@ requires array_list(this; ?size, ?cnt, ?data);
//@ ensures array_list(this; size, cnt, data) &*& result == cnt;
short getCount()
{
    return count;
}

/*@ lemma void array_list_add_success(ArrayList l; short size, short cnt, byte val)
    requires array_list(l; size, cnt, ?data) &*& cnt < size;
    ensures array_list(l; size, cnt + 1, ?data2) &*& data2[cnt] == val;
{
    open array_list(l; size, cnt, data);
    l.elems[cnt] = val;
    assert l.count |-> cnt;
    l.count = (short)(cnt + 1);
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
}

class Program {
    //@ requires true;
    //@ ensures true;
    static void test()
        //@ requires true;
        //@ ensures true;
    {
        ArrayList list = new ArrayList((short) 10);
        //@ close array_list(list; 10, 0, nil);
        if (list.add((byte) 1) && list.add((byte) 2) && list.add((byte) 3)) {
            //@ open array_list(list; 10, 3, ?data);
            short count = list.getCount();
            //@ assert count == 3;
            assert count == 3;
            list.get((short) 2);
        }
    }
}