






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
}

class BackupCell extends CellImpl {
}

class BackupCellWrapper extends CellImpl {
  boolean b;
  int myvalue;
}

class Test {
  void test1(CellImpl c) 
    
    
  {
    c.value = 5;
  }
  
  void test2(BackupCellWrapper c) 
    
    
  {
    if(! c.b) {
      c.value = 5;
    } else {
      c.myvalue = 10;
    }
  }
}
