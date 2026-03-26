public class LocalClass_desugared
{
  //@ requires true;
  //@ ensures true;
  public static void main(String[] args)
    
    
  {
    //@ close LocalClass_desugared$1InnerClass_pred(new LocalClass_desugared$1InnerClass(), 1);
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
    
  //@ predicate LocalClass_desugared$1InnerClass_pred(LocalClass_desugared$1InnerClass this, int xv) = this.x |-> xv;
    
  //@ requires true;
  //@ ensures LocalClass_desugared$1InnerClass_pred(this, 1);
  LocalClass_desugared$1InnerClass()    
    
    
  {
    super();
    //@ close LocalClass_desugared$1InnerClass_pred(this, 1);
  }
    
  //@ requires LocalClass_desugared$1InnerClass_pred(this, ?xv);
  //@ ensures LocalClass_desugared$1InnerClass_pred(this, xv) &*& result == xv;
  int getX()    
    
    
  {
    //@ open LocalClass_desugared$1InnerClass_pred(this, xv);
    return this.x;
    //@ close LocalClass_desugared$1InnerClass_pred(this, xv);
  }
    
  //@ requires LocalClass_desugared$1InnerClass_pred(this, _);
  //@ ensures LocalClass_desugared$1InnerClass_pred(this, i);
  void setX(int i)    
    
    
  {
    //@ open LocalClass_desugared$1InnerClass_pred(this, _);
    x = i;
    //@ close LocalClass_desugared$1InnerClass_pred(this, i);
  }
}