public class LocalClass_desugared
{
  //@ requires true;
  //@ ensures true;
  public static void main(String[] args)
  {
    LocalClass_desugared$1InnerClass first = new LocalClass_desugared$1InnerClass();
    first.setX(111);
    int i = first.getX();
    
  }
}

/*@
predicate LocalClass_desugared$1InnerClass_obj(LocalClass_desugared$1InnerClass this, int x) = 
  this.x |-> x;
@*/
class LocalClass_desugared$1InnerClass 
{
  int x = 1;
    
  //@ requires true;
  //@ ensures LocalClass_desugared$1InnerClass_obj(this, 1);
  LocalClass_desugared$1InnerClass()    
  {
    //@ close LocalClass_desugared$1InnerClass_obj(this, 1);
    super();
    
  }
    
  //@ requires LocalClass_desugared$1InnerClass_obj(this, ?vx);
  //@ ensures LocalClass_desugared$1InnerClass_obj(this, vx) &*& result == vx;
  int getX()    
  {
    //@ open LocalClass_desugared$1InnerClass_obj(this, ?vx);
    int ret = this.x;
    //@ close LocalClass_desugared$1InnerClass_obj(this, vx);
    return ret;
  }
    
  //@ requires LocalClass_desugared$1InnerClass_obj(this, ?vx);
  //@ ensures LocalClass_desugared$1InnerClass_obj(this, i);
  void setX(int i)    
  {
    //@ open LocalClass_desugared$1InnerClass_obj(this, ?vx);
    x = i;
    //@ close LocalClass_desugared$1InnerClass_obj(this, i);
  }
}