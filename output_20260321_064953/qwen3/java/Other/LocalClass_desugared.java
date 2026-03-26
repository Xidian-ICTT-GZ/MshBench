public class LocalClass_desugared
{
  public static void main(String[] args)
    
    
  {
    //@ predicate InnerClass_own(LocalClass_desugared$1InnerClass obj; int val) = obj.x |-> val;
    LocalClass_desugared$1InnerClass first = new LocalClass_desugared$1InnerClass();
    //@ close InnerClass_own(first, 1);
    first.setX(111);
    //@ open InnerClass_own(first, _);
    //@ close InnerClass_own(first, 111);
    int i = first.getX();
    //@ open InnerClass_own(first, _);
    
  }
}

class LocalClass_desugared$1InnerClass 
{
  
  
  int x = 1;
    
  LocalClass_desugared$1InnerClass()    
    
    
  {
    super();
    
  }
    
  /*@
  predicate inner_own(int val) = this.x |-> val;
  @*/
  //@ requires inner_own(?v);
  //@ ensures inner_own(v) &*& result == v;
  int getX()    
    
    
  {
    
    return this.x;
  }
    
  //@ requires inner_own(?v);
  //@ ensures inner_own(i);
  void setX(int i)    
    
    
  {
    //@ open inner_own(v);
    x = i;
    //@ close inner_own(i);
  }
}