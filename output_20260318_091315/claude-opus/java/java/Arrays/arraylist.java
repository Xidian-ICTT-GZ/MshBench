class ArrayList {
  /*@ 
  predicate ArrayListInv(ArrayList this, int size, int count, list<byte> elemsList) = 
    this.elems |-> ?elems &*& elems.length == size &*& 
    0 <= count &*& count <= size &*& 
    this.count |-> count &*&
    array_slice(elems, 0, count, elemsList) &*&
    array_slice(elems, count, size, ?suffix) &*& suffix == nil;
  @*/

  byte[] elems;
  short count;

  //@ requires size >= 0 &*& size <= 32767;
  //@ ensures ArrayListInv(this, size, 0, nil);
  ArrayList(short size) {
    elems = new byte[size];
    count = 0;
  }

  //@ requires ArrayListInv(this, ?size, ?count, ?elemsList);
  //@ ensures ArrayListInv(this, size, count, elemsList) &*& result == count;
  short getCount() {
    return count;
  }

  //@ requires ArrayListInv(this, ?size, ?count, ?elemsList) &*& 0 <= index &*& index < count;
  //@ ensures ArrayListInv(this, size, count, elemsList) &*& result == nth(index, elemsList);
  byte get(short index) {
    return elems[index];
  }

  //@ requires ArrayListInv(this, ?size, ?count, ?elemsList) &*& count <= size;
  //@ ensures
  //@   (count == size
  //@     ? (ArrayListInv(this, size, count, elemsList) &*& result == false)
  //@     : (
  //@       ArrayListInv(this, size, count + 1, elemsList + cons(value, nil)) &*& result == true
  //@     )
  //@   );
  boolean add(byte value) {
    if (count == elems.length)
      return false;
    elems[count++] = value;
    return true;
  }
}

class Program {
  //@ requires true;
  //@ ensures true;
  static void test() {
    ArrayList list = new ArrayList((short)10);
    if (list.add((byte)1) && list.add((byte)2) && list.add((byte)3)) {
      short count = list.getCount();
      assert count == 3;
      list.get((short)2);
    }
  }
}