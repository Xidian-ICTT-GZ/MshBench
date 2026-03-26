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
  int value;
  //@ predicate valid() = this.value |-> _;
}

class BackupCell extends CellImpl {
  //@ predicate valid() = super.valid();
}

class BackupCellWrapper extends CellImpl {
  boolean b;
  int myvalue;
  //@ predicate valid() = super.valid() &*& this.b |-> _ &*& this.myvalue |-> _;
}

class Test {
  //@ requires c != null &*& c.valid();
  //@ ensures c.valid();
  void test1(CellImpl c)
  {
    c.value = 5;
  }

  //@ requires c != null &*& c.valid();
  //@ ensures c.valid();
  void test2(BackupCellWrapper c)
  {
    if(! c.b) {
      c.value = 5;
    } else {
      c.myvalue = 10;
    }
  }
}