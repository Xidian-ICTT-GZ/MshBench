/*@ predicate cellImpl(CellImpl c; int v) = c.value |-> v; @*/
/*@ predicate backupCellWrapper(BackupCellWrapper c; int v1, int v2, boolean bval) =
    c.value |-> v1 &*& c.myvalue |-> v2 &*& c.b |-> bval;
@*/

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
  //@ requires cellImpl(c, _);
  //@ ensures cellImpl(c, 5);
  void test1(CellImpl c) 
  {
    c.value = 5;
  }
  
  //@ requires backupCellWrapper(c, _, _, false);
  //@ ensures backupCellWrapper(c, 5, _, false);
  //@ requires backupCellWrapper(c, _, _, true);
  //@ ensures backupCellWrapper(c, _, 10, true);
  void test2(BackupCellWrapper c) 
  {
    if(! c.b) {
      c.value = 5;
    } else {
      c.myvalue = 10;
    }
  }
}