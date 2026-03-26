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

/*@
predicate CellImpl_inv(CellImpl c; int v) = c.value |-> v;
@*/
class CellImpl implements Cell {
  int value;
}

class BackupCell extends CellImpl {
}

/*@
predicate BackupCellWrapper_inv(BackupCellWrapper c; boolean bVal, int v, int myv) = 
  c.b |-> bVal &*& c.value |-> v &*& c.myvalue |-> myv &*& CellImpl_inv(c, v);
@*/
class BackupCellWrapper extends CellImpl {
  boolean b;
  int myvalue;
}

class Test {
  void test1(CellImpl c) 
  //@ requires c != null &*& CellImpl_inv(c, _);
  //@ ensures CellImpl_inv(c, 5);
  {
    //@ open CellImpl_inv(c, _);
    c.value = 5;
    //@ close CellImpl_inv(c, 5);
  }
  
  void test2(BackupCellWrapper c) 
  //@ requires c != null &*& BackupCellWrapper_inv(c, _, _, _);
  //@ ensures BackupCellWrapper_inv(c, c.b, (c.b ? old_value : 5), (c.b ? 10 : old_myvalue));
  {
    //@ open BackupCellWrapper_inv(c, ?bVal, ?old_value, ?old_myvalue);
    if(! c.b) {
      c.value = 5;
      //@ close BackupCellWrapper_inv(c, false, 5, old_myvalue);
    } else {
      c.myvalue = 10;
      //@ close BackupCellWrapper_inv(c, true, old_value, 10);
    }
  }
}