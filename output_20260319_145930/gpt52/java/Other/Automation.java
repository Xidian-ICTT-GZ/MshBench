class Automation {
  //@ requires true;
  //@ ensures true;
  void test1()
  {
  }

  //@ requires true;
  //@ ensures true;
  void test2()
  {
  }
}

interface Cell {
}

class CellImpl implements Cell {
  public int value;
}

class BackupCell extends CellImpl {
}

class BackupCellWrapper extends CellImpl {
  public boolean b;
  public int myvalue;
}

class Test {
  //@ requires c != null &*& c.value |-> _;
  //@ ensures c.value |-> 5;
  void test1(CellImpl c)
  {
    c.value = 5;
  }

  //@ requires c != null &*& c.b |-> ?b &*& c.value |-> ?v &*& c.myvalue |-> ?mv;
  //@ ensures c.b |-> b &*& (b ? (c.value |-> v &*& c.myvalue |-> 10) : (c.value |-> 5 &*& c.myvalue |-> mv));
  void test2(BackupCellWrapper c)
  {
    if (!c.b) {
      c.value = 5;
    } else {
      c.myvalue = 10;
    }
  }
}