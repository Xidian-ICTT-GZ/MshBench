class ArrayList {
byte[] elems;
short count;

//@ predicate array_list(ArrayList l; short size, short cnt, byte* data) = 
//@     l.elems |-> ?a &*& array_block(a, size) &*&
//@     l.count |-> cnt &*& 0 <= cnt &*& cnt <= size &*&
//@     length(a) == size &*& cnt <= size &*& cnt == length(slice(data, 0, cnt)) &*& 
//@     array_contents(a, 0, cnt, data);
//@     // Note: array_contents is a common predicate for array contents

//@ requires 0 <= size &*& size <= Short.MAX_VALUE;
//@ ensures array_list(this, size, 0, _);
ArrayList(short size)
{
    elems = new byte[size];
    count = 0;
}

//@ requires array_list(this, ?size, ?cnt, ?data) &*& 0 <= index &*& index < size;
//@ ensures array_list(this, size, cnt, data) &*& result == data[index];
byte get(short index)
{
    return elems[index];
}

//@ requires array_list(this, ?size, ?cnt, ?data) &*& 0 <= cnt &*& cnt <= size;
//@ ensures (cnt < size ==> result == true &*& array_list(this, size, cnt + 1, append(data, result)) ) &*&
//@         (cnt == size ==> result == false &*& array_list(this, size, cnt, data));
boolean add(byte value)
{
    if (count == elems.length)
        return false;
    elems[count++] = value;
    return true;
}

//@ requires array_list(this, ?size, ?cnt, ?data);
//@ ensures array_list(this, size, cnt, data) &*& result == cnt;
short getCount()
{
    return count;
}
}

/*@ predicate array_contents(byte[] a, int start, int end, byte* data) =
    start == end ? emp : 
    a[start] |-> hd &*& array_contents(a, start + 1, end, data + 1);
*/

/*@ lemma void array_list_add_success(ArrayList l; short size, short cnt, byte val)
    requires array_list(l, size, cnt, ?data) &*& cnt < size;
    ensures array_list(l, size, cnt + 1, ?data') &*& data'[cnt] == val;
{
    open array_list(l, size, cnt, data);
    open array_contents(l.elems, 0, size, data);
    l.elems[cnt] = val;
    close array_contents(l.elems, 0, cnt + 1, data' /* with val at cnt */);
    close array_contents(l.elems, cnt + 1, size, data + cnt + 1);
    close array_list(l, size, cnt + 1, data');
}
*/

/*@ lemma void array_list_add_fail(ArrayList l; short size, short cnt)
    requires array_list(l, size, cnt, ?data) &*& cnt == size;
    ensures array_list(l, size, cnt, data);
{
    open array_list(l, size, cnt, data);
    close array_list(l, size, cnt, data);
}
*/

class Program {
    //@ requires true;
    //@ ensures true;
    static void test()
    {
        ArrayList list = new ArrayList((short) 10);
        //@ close array_list(list, 10, 0, ?data);
        if (list.add((byte) 1) && list.add((byte) 2) && list.add((byte) 3)) {
            //@ open array_list(list, 10, 3, ?data);
            short count = list.getCount();
            //@ assert count == 3;
            assert count == 3;
            list.get((short) 2);
            //@ close array_list(list, 10, 3, ?data);
        }
    }
}