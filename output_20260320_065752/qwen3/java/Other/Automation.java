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

/*@ 
predicate cellImpl(CellImpl c; int v) = c.value |-> v;
predicate backupCellWrapper(BackupCellWrapper c; int v, boolean bval, int mv) = 
  c.value |-> v &*& c.b |-> bval &*& c.myvalue |-> mv;
@*/

class Test {
  //@ requires cellImpl(c, _);
  //@ ensures cellImpl(c, 5);
  void test1(CellImpl c) 
    
    
  {
    //@ open cellImpl(c, _);
    c.value = 5;
    //@ close cellImpl(c, 5);
  }
  
  //@ requires backupCellWrapper(c, _, ?bval, ?mv);
  //@ ensures backupCellWrapper(c, ?v, bval, ?mv2);
  void test2(BackupCellWrapper c) 
    
    
  {
    //@ open backupCellWrapper(c, _, bval, mv);
    if(! c.b) {
      c.value = 5;
      //@ close backupCellWrapper(c, 5, bval, mv);
    } else {
      c.myvalue = 10;
      //@ close backupCellWrapper(c, _, bval, 10);
    }
  }
}