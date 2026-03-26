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
}

class BackupCell extends CellImpl {
}

class BackupCellWrapper extends CellImpl {
  boolean b;
  int myvalue;
}

class Test {
  void test1(CellImpl c) 
  //@ requires c != null &*& c.value |-> _;
  //@ ensures c.value |-> 5;
  {
    c.value = 5;
  }
  
  void test2(BackupCellWrapper c) 
  //@ requires c != null &*& c.b |-> _ &*& c.value |-> _ &*& c.myvalue |-> _;
  //@ ensures c.b |-> ?b &*& (b ? c.myvalue |-> 10 &*& c.value |-> _ : c.value |-> 5 &*& c.myvalue |-> _);
  {
    if(! c.b) {
      c.value = 5;
    } else {
      c.myvalue = 10;
    }
  }
}