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
  /*@ predicate cell() = true; @*/
}

class CellImpl implements Cell {
  int value;
  
  //@ predicate cellimpl(int v) = this.value |-> v;
}

class BackupCell extends CellImpl {
  //@ predicate backupcell(int v) = cellimpl(v);
}

class BackupCellWrapper extends CellImpl {
  boolean b;
  int myvalue;
  
  //@ predicate backupcellwrapper(boolean bb, int v, int mv) = this.value |-> v &*& this.b |-> bb &*& this.myvalue |-> mv;
}

class Test {
  void test1(CellImpl c) 
  //@ requires c.cellimpl(?v);
  //@ ensures c.cellimpl(5);
  {
    c.value = 5;
  }
  
  void test2(BackupCellWrapper c) 
  //@ requires c.backupcellwrapper(?bb, ?v, ?mv);
  //@ ensures c.backupcellwrapper(bb, (bb == false ? 5 : v), (bb == true ? 10 : mv));
  {
    if(! c.b) {
      c.value = 5;
    } else {
      c.myvalue = 10;
    }
  }
}