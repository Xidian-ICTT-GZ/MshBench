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
}

class BackupCell extends CellImpl {
}

class BackupCellWrapper extends CellImpl {
  boolean b;
  int myvalue;
}

class Test {
  //@ requires c != null;
  //@ ensures true;
  void test1(CellImpl c) 
    
    
  {
    c.value = 5;
  }
  
  //@ requires c != null;
  //@ ensures true;
  void test2(BackupCellWrapper c) 
    
    
  {
    if(! c.b) {
      c.value = 5;
    } else {
      c.myvalue = 10;
    }
  }
}