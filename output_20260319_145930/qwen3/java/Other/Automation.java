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

/*@ predicate cellImpl(CellImpl c; int v) = c.value |-> v; @*/

/*@ predicate backupCell(BackupCell c; int v) = cellImpl(c, v); @*/

/*@ predicate backupCellWrapper(BackupCellWrapper c; int v1, int v2, boolean bval) =
      c.value |-> v1 &*& c.myvalue |-> v2 &*& c.b |-> bval;
@*/

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
    //@ open cellImpl(c, _);
    c.value = 5;
    //@ close cellImpl(c, 5);
  }
  
  //@ requires backupCellWrapper(c, _, _, ?bval);
  //@ ensures backupCellWrapper(c, bval ? c.value : 5, bval ? 10 : c.myvalue, bval);
  void test2(BackupCellWrapper c) 
  {
    //@ open backupCellWrapper(c, ?v1, ?v2, ?bval);
    if(! c.b) {
      c.value = 5;
    } else {
      c.myvalue = 10;
    }
    //@ close backupCellWrapper(c, c.value, c.myvalue, bval);
  }
}