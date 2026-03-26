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
  /*@ 
  predicate valid() = this->value |-> _;
  @*/
}

class BackupCell extends CellImpl {
}

class BackupCellWrapper extends CellImpl {
  boolean b;
  int myvalue;
  /*@ 
  predicate valid() = this->b |-> _ &*& this->myvalue |-> _ &*& this->value |-> _;
  @*/
}

class Test {
  void test1(CellImpl c) 
  //@ requires c.valid();
  //@ ensures c.valid();
  {
    //@ open c.valid();
    c.value = 5;
    //@ close c.valid();
  }
  
  void test2(BackupCellWrapper c) 
  //@ requires c.valid();
  //@ ensures c.valid();
  {
    //@ open c.valid();
    if(! c.b) {
      c.value = 5;
    } else {
      c.myvalue = 10;
    }
    //@ close c.valid();
  }
}