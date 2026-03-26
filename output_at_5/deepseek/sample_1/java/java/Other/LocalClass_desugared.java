public class LocalClass_desugared
{
  //@ predicate LocalClass_desugared$1InnerClass_own(int x) = this.x |-> x;
  
  public static void main(String[] args)
    
    
  {
    //@ close LocalClass_desugared$1InnerClass_own(1);
    LocalClass_desugared$1InnerClass first = new LocalClass_desugared$1InnerClass();
    //@ open LocalClass_desugared$1InnerClass_own(_);
    first.setX(111);
    //@ open LocalClass_desugared$1InnerClass_own(_);
    int i = first.getX();
    //@ close LocalClass_desugared$1InnerClass_own(_);
    
  }
}

class LocalClass_desugared$1InnerClass 
{
  
  
  int x = 1;
    
  LocalClass_desugared$1InnerClass()    
    
    
  {
    super();
    
  }
    
  int getX()    
  //@ requires LocalClass_desugared$1InnerClass_own(?v);
  //@ ensures LocalClass_desugared$1InnerClass_own(v) &*& result == v;
    
  {
    //@ open LocalClass_desugared$1InnerClass_own(v);
    return this.x;
    //@ close LocalClass_desugared$1InnerClass_own(v);
  }
    
  void setX(int i)    
  //@ requires LocalClass_desugared$1InnerClass_own(_);
  //@ ensures LocalClass_desugared$1InnerClass_own(i);
    
  {
    //@ open LocalClass_desugared$1InnerClass_own(_);
    x = i;
    //@ close LocalClass_desugared$1InnerClass_own(i);
  }
}