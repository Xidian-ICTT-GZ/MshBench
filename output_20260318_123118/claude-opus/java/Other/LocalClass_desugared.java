public class LocalClass_desugared
{
  //@ requires true;
  //@ ensures true;
  public static void main(String[] args)
  {
    LocalClass_desugared$1InnerClass first = new LocalClass_desugared$1InnerClass();
    /*@ close LocalClass_desugared$1InnerClass(first, 1); @*/
    first.setX(111);
    int i = first.getX();
  }
}

class LocalClass_desugared$1InnerClass 
{
  int x = 1;
  
  /*@ predicate LocalClass_desugared$1InnerClass(LocalClass_desugared$1InnerClass this, int x_value) = 
        this.x |-> x_value;
  @*/

  //@ requires true;
  //@ ensures LocalClass_desugared$1InnerClass(this, 1);
  LocalClass_desugared$1InnerClass()    
  {
    super();
  }
    
  //@ requires LocalClass_desugared$1InnerClass(this, ?vx);
  //@ ensures  LocalClass_desugared$1InnerClass(this, vx) &*& result == vx;
  int getX()    
  { 
    return this.x;
  }
    
  //@ requires LocalClass_desugared$1InnerClass(this, ?vx);
  //@ ensures  LocalClass_desugared$1InnerClass(this, i);
  void setX(int i)    
  {
    x = i;
  }
}