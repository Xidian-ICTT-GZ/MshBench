/*@
predicate LocalClass_desugared$1InnerClass_pred(LocalClass_desugared$1InnerClass obj; int x) =
    obj.x |-> x;
@*/

public class LocalClass_desugared
{
  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
  {
    LocalClass_desugared$1InnerClass first = new LocalClass_desugared$1InnerClass();
    //@ open LocalClass_desugared$1InnerClass_pred(first, _);
    first.setX(111);
    //@ open LocalClass_desugared$1InnerClass_pred(first, _);
    int i = first.getX();
    //@ open LocalClass_desugared$1InnerClass_pred(first, _);
  }
}

class LocalClass_desugared$1InnerClass 
{
  
  
  int x = 1;
    
  LocalClass_desugared$1InnerClass()    
    //@ requires true;
    //@ ensures LocalClass_desugared$1InnerClass_pred(this, 1);
  {
    super();
    //@ close LocalClass_desugared$1InnerClass_pred(this, 1);
  }
    
  int getX()    
    //@ requires this.x |-> ?v;
    //@ ensures this.x |-> v &*& result == v;
  {
    
    return this.x;
  }
    
  void setX(int i)    
    //@ requires this.x |-> _;
    //@ ensures LocalClass_desugared$1InnerClass_pred(this, i);
  {
    x = i;
    //@ close LocalClass_desugared$1InnerClass_pred(this, i);
  }
}