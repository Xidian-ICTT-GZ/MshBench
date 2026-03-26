public class LocalClass_desugared
{
  //@ requires true;
  //@ ensures true;
  public static void main(String[] args)
  {
    LocalClass_desugared$1InnerClass first = new LocalClass_desugared$1InnerClass();
    //@ close LocalClass_desugared$1InnerClass_pred(first, _);
    first.setX(111);
    int i = first.getX();
    
  }
}

class LocalClass_desugared$1InnerClass 
{
  /*@
  predicate LocalClass_desugared$1InnerClass_pred(int xval) =
    x |-> xval;
  @*/
  
  int x = 1;
    
  //@ requires true;
  //@ ensures LocalClass_desugared$1InnerClass_pred(1);
  LocalClass_desugared$1InnerClass()    
  {
    super();
    //@ close LocalClass_desugared$1InnerClass_pred(1);
  }
    
  //@ requires LocalClass_desugared$1InnerClass_pred(?xval);
  //@ ensures LocalClass_desugared$1InnerClass_pred(xval) &*& result == xval;
  int getX()    
  {
    //@ open LocalClass_desugared$1InnerClass_pred(_);
    //@ close LocalClass_desugared$1InnerClass_pred(this.x);
    return this.x;
  }
    
  //@ requires LocalClass_desugared$1InnerClass_pred(?old_x);
  //@ ensures LocalClass_desugared$1InnerClass_pred(i);
  void setX(int i)    
  {
    //@ open LocalClass_desugared$1InnerClass_pred(_);
    x = i;
    //@ close LocalClass_desugared$1InnerClass_pred(i);
  }
}