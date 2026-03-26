class ArrayList {
byte[] elems;
short count;

//@ requires 0 <= size &*& size <= Short.MAX_VALUE;
//@ ensures true;
//@ ensures elems |-> ?a &*& array_block(a, size) &*& count |-> (short)0 &*& length(a) == size;
ArrayList(short size)
{
    elems = new byte[size];
}

//@ requires this.elems |-> ?a &*& array_block(a, length(a)) &*& this.count |-> ?cnt &*& 0 <= cnt &*& cnt <= length(a);
//@ ensures this.count |-> cnt &*& result == cnt;
short getCount()
{
    return count;
}

//@ requires this.elems |-> ?a &*& array_block(a, length(a)) &*& 0 <= index &*& index < length(a) &*& this.count |-> ?cnt &*& 0 <= cnt &*& cnt <= length(a);
//@ ensures this.elems |-> a &*& array_block(a, length(a)) &*& this.count |-> cnt &*& result == a[index];
byte get(short index)
{
    return elems[index];
}

//@ requires this.elems |-> ?a &*& array_block(a, length(a)) &*& this.count |-> ?cnt &*& 0 <= cnt &*& cnt <= length(a);
//@ ensures (cnt < length(a) ==> (result == true &*& this.count |-> cnt + 1 &*& a[cnt] == value)) &*&
//@         (cnt == length(a) ==> (result == false &*& this.count |-> cnt)) &*& this.elems |-> a &*& array_block(a, length(a));
boolean add(byte value)
{
    if (count == elems.length)
        return false;
    elems[count++] = value;
    return true;
}

/*@ predicate array_list(ArrayList l; short size, short cnt, byte* data) =
    l.elems |-> ?a &*&
    array_block(a, size) &*&
    l.count |-> cnt &*&
    0 <= cnt &*& cnt <= size &*&
    cnt == length(a);
@*/

/*@ lemma void array_list_add_success(ArrayList l; short size, short cnt, byte val)
    requires array_list(l; size, cnt, ?data) &*& cnt < size;
    ensures array_list(l; size, cnt + 1, ?data') &*& data'[cnt] == val;
{
    open array_list(l; size, cnt, data);
    assert l.elems |-> ?a &*& array_block(a, size) &*& l.count |-> cnt;
    l.elems[cnt] = val;
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