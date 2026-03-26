public class LocalClass_desugared
{
  //@ requires true;
  //@ ensures true;
  public static void main(String[] args)
    
    
  {
    //@ close LocalClass_desugared$1InnerClass_pred(new LocalClass_desugared$1InnerClass(), 1);
    LocalClass_desugared$1InnerClass first = new LocalClass_desugared$1InnerClass();
    //@ open LocalClass_desugared$1InnerClass_pred(first, _);
    //@ close LocalClass_desugared$1InnerClass_pred(first, 111);
    first.setX(111);
    //@ open LocalClass_desugared$1InnerClass_pred(first, _);
    int i = first.getX();
    //@ close LocalClass_desugared$1InnerClass_pred(first, i);
    
  }
}

/*@
predicate LocalClass_desugared$1InnerClass_pred(LocalClass_desugared$1InnerClass c, int x) = c.x |-> x;
@*/

class LocalClass_desugared$1InnerClass 
{
  
  
  int x = 1;
    
  //@ requires true;
  //@ ensures LocalClass_desugared$1InnerClass_pred(this, 1);
  LocalClass_desugared$1InnerClass()    
    
    
  {
    super();
    
  }
    
  //@ requires LocalClass_desugared$1InnerClass_pred(this, ?x);
  //@ ensures LocalClass_desugared$1InnerClass_pred(this, x) &*& result == x;
  int getX()    
    
    
  {
    
    return this.x;
  }
    
  //@ requires LocalClass_desugared$1InnerClass_pred(this, _);
  //@ ensures LocalClass_desugared$1InnerClass_pred(this, i);
  void setX(int i)    
    
    
  {
    x = i;
  }
}