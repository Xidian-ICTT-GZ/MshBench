class Automation {
  void test1() 
  //@ requires true;
  //@ ensures true;
  {
  }
  
  void test2()
  //@ requires true;
  //@ ensures true;
  {
  }
}

interface Cell {
}

class CellImpl implements Cell {
  int value;
  /*@
  predicate objectInv() = this->value |-> _;
  @*/
}

class BackupCell extends CellImpl {
  /*@
  predicate objectInv() = this->value |-> _;
  @*/
}

class BackupCellWrapper extends CellImpl {
  boolean b;
  int myvalue;
  /*@
  predicate objectInv() = this->value |-> _ &*& this->b |-> _ &*& this->myvalue |-> _;
  @*/
}

class Test {
  void test1(CellImpl c) 
  //@ requires c.objectInv();
  //@ ensures c.objectInv();
  {
    c.value = 5;
  }
  
  void test2(BackupCellWrapper c) 
  //@ requires c.objectInv();
  //@ ensures c.objectInv();
  {
    if(! c.b) {
      c.value = 5;
    } else {
      c.myvalue = 10;
    }
  }
}