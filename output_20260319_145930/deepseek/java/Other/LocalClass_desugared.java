public class LocalClass_desugared
{
  //@ predicate LocalClass_desugared$1InnerClass(int x) = this.x |-> x;
  
  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
  {
    //@ close LocalClass_desugared$1InnerClass(1);
    LocalClass_desugared$1InnerClass first = new LocalClass_desugared$1InnerClass();
    //@ open LocalClass_desugared$1InnerClass(_);
    first.setX(111);
    //@ open LocalClass_desugared$1InnerClass(_);
    int i = first.getX();
    //@ close LocalClass_desugared$1InnerClass(_);
    
  }
}

class LocalClass_desugared$1InnerClass 
{
  int x = 1;
    
  LocalClass_desugared$1InnerClass()    
    //@ requires true;
    //@ ensures LocalClass_desugared$1InnerClass(1);
  {
    super();
    //@ close LocalClass_desugared$1InnerClass(1);
  }
    
  int getX()    
    //@ requires LocalClass_desugared$1InnerClass(?x);
    //@ ensures LocalClass_desugared$1InnerClass(x) &*& result == x;
  {
    //@ open LocalClass_desugared$1InnerClass(x);
    return this.x;
    //@ close LocalClass_desugared$1InnerClass(x);
  }
    
  void setX(int i)    
    //@ requires LocalClass_desugared$1InnerClass(_);
    //@ ensures LocalClass_desugared$1InnerClass(i);
  {
    //@ open LocalClass_desugared$1InnerClass(_);
    x = i;
    //@ close LocalClass_desugared$1InnerClass(i);
  }
}