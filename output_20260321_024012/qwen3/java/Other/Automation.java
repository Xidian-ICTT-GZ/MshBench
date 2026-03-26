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
predicate backupCellWrapper(BackupCellWrapper c; int v1, int v2, bool b1) = 
  c.value |-> v1 &*& c.myvalue |-> v2 &*& c.b |-> b1;
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
  
  //@ requires backupCellWrapper(c, _, _, _);
  //@ ensures backupCellWrapper(c, ?v1, ?v2, ?b1);
  void test2(BackupCellWrapper c) 
    
    
  {
    //@ open backupCellWrapper(c, ?old_v1, ?old_v2, ?old_b);
    if(! c.b) {
      c.value = 5;
      //@ close backupCellWrapper(c, 5, old_v2, old_b);
    } else {
      c.myvalue = 10;
      //@ close backupCellWrapper(c, old_v1, 10, old_b);
    }
  }
}