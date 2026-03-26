class Automation {
  void test1() 
    
    
  {
    
  }
  
  void test2()
    
    
  {
     
  }
}

interface Cell {
}

class CellImpl implements Cell {
  int value;
  
  //@ predicate CellImpl() = value |-> _;
  
  //@ requires true;
  //@ ensures CellImpl();
  CellImpl() {
    //@ close CellImpl();
  }
}

class BackupCell extends CellImpl {
  //@ predicate BackupCell() = CellImpl();
  
  //@ requires true;
  //@ ensures BackupCell();
  BackupCell() {
    //@ close BackupCell();
  }
}

class BackupCellWrapper extends CellImpl {
  boolean b;
  int myvalue;
  
  //@ predicate BackupCellWrapper() = CellImpl() &*& b |-> _ &*& myvalue |-> _;
  
  //@ requires true;
  //@ ensures BackupCellWrapper();
  BackupCellWrapper() {
    //@ close BackupCellWrapper();
  }
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
      c.value = 5;
    } else {
      c.myvalue = 10;
    }
    //@ close c.BackupCellWrapper();
  }
}