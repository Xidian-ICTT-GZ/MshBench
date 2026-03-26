public class LocalClass_desugared
{
  //@ requires true;
  //@ ensures true;
  public static void main(String[] args)
    
    
  {
    //@ close LocalClass_desugared$1InnerClass_pred(new LocalClass_desugared$1InnerClass());
    LocalClass_desugared$1InnerClass first = new LocalClass_desugared$1InnerClass();
    //@ open LocalClass_desugared$1InnerClass_pred(first);
    first.setX(111);
    //@ open LocalClass_desugared$1InnerClass_pred(first);
    int i = first.getX();
    //@ open LocalClass_desugared$1InnerClass_pred(first);
    
  }
}

/*@
predicate LocalClass_desugared$1InnerClass_pred(LocalClass_desugared$1InnerClass c) = c.x |-> _;
@*/

class LocalClass_desugared$1InnerClass 
{
  
  
  int x = 1;
    
  //@ requires true;
  //@ ensures LocalClass_desugared$1InnerClass_pred(this);
  LocalClass_desugared$1InnerClass()    
    
    
  {
    super();
    //@ close LocalClass_desugared$1InnerClass_pred(this);
  }
    
  //@ requires LocalClass_desugared$1InnerClass_pred(this);
  //@ ensures LocalClass_desugared$1InnerClass_pred(this) &*& result == this.x;
  int getX()    
    
    
  {
    //@ open LocalClass_desugared$1InnerClass_pred(this);
    return this.x;
    //@ close LocalClass_desugared$1InnerClass_pred(this);
  }
    
  //@ requires LocalClass_desugared$1InnerClass_pred(this);
  //@ ensures LocalClass_desugared$1InnerClass_pred(this) &*& this.x == i;
  void setX(int i)    
    
    
  {
    //@ open LocalClass_desugared$1InnerClass_pred(this);
    x = i;
    //@ close LocalClass_desugared$1InnerClass_pred(this);
  }
}