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
  //@ predicate CellImpl() = value |-> _;
}

class BackupCell extends CellImpl {
  //@ predicate BackupCell() = CellImpl();
}

class BackupCellWrapper extends CellImpl {
  boolean b;
  int myvalue;
  //@ predicate BackupCellWrapper() = CellImpl() &*& b |-> _ &*& myvalue |-> _;
}

class Test {
  void test1(CellImpl c) 
  //@ requires c.CellImpl();
  //@ ensures c.CellImpl();
  {
    //@ open c.CellImpl();
    c.value = 5;
    //@ close c.CellImpl();
  }
  
  void test2(BackupCellWrapper c) 
  //@ requires c.BackupCellWrapper();
  //@ ensures c.BackupCellWrapper();
  {
    //@ open c.BackupCellWrapper();
    if(! c.b) {
      //@ open CellImpl();
      c.value = 5;
      //@ close CellImpl();
    } else {
      c.myvalue = 10;
    }
    //@ close c.BackupCellWrapper();
  }
}