public class LocalClass_desugared
{
  //@ requires true;
  //@ ensures true;
  public static void main(String[] args)
    
    
  {
    //@ close Class_invariant_LocalClass_desugared$1InnerClass();
    LocalClass_desugared$1InnerClass first = new LocalClass_desugared$1InnerClass();
    first.setX(111);
    int i = first.getX();
    
  }
  
  //@ predicate Class_invariant_LocalClass_desugared$1InnerClass() = true;
}

class LocalClass_desugared$1InnerClass 
{
  
  
  int x = 1;
    
  //@ requires true;
  //@ ensures Class_invariant_LocalClass_desugared$1InnerClass();
  LocalClass_desugared$1InnerClass()    
    
    
  {
    super();
    //@ close Class_invariant_LocalClass_desugared$1InnerClass();
  }
    
  //@ requires Class_invariant_LocalClass_desugared$1InnerClass();
  //@ ensures Class_invariant_LocalClass_desugared$1InnerClass() &*& result == this.x;
  int getX()    
    
    
  {
    //@ open Class_invariant_LocalClass_desugared$1InnerClass();
    return this.x;
    //@ close Class_invariant_LocalClass_desugared$1InnerClass();
  }
    
  //@ requires Class_invariant_LocalClass_desugared$1InnerClass();
  //@ ensures Class_invariant_LocalClass_desugared$1InnerClass();
  void setX(int i)    
    
    
  {
    //@ open Class_invariant_LocalClass_desugared$1InnerClass();
    x = i;
    //@ close Class_invariant_LocalClass_desugared$1InnerClass();
  }
  
  //@ predicate Class_invariant_LocalClass_desugared$1InnerClass() = true;
}