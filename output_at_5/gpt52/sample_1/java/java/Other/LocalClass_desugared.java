public class LocalClass_desugared
{
  public static void main(String[] args)
  //@ requires true;
  //@ ensures true;
    
    
  {
    LocalClass_desugared$1InnerClass first = new LocalClass_desugared$1InnerClass();
    //@ close LocalClass_desugared$1InnerClass_state(first, 1);
    first.setX(111);
    int i = first.getX();
    //@ open LocalClass_desugared$1InnerClass_state(first, i);
    
  }
}

/*@
predicate LocalClass_desugared$1InnerClass_state(LocalClass_desugared$1InnerClass obj; int x) =
  obj.x |-> x;
@*/

class LocalClass_desugared$1InnerClass 
{
  
  
  int x = 1;
    
  LocalClass_desugared$1InnerClass()    
  //@ requires true;
  //@ ensures LocalClass_desugared$1InnerClass_state(this, 1);
    
    
  {
    super();
    //@ close LocalClass_desugared$1InnerClass_state(this, 1);
    
  }
    
  int getX()    
  //@ requires LocalClass_desugared$1InnerClass_state(this, ?x);
  //@ ensures LocalClass_desugared$1InnerClass_state(this, x) &*& result == x;
    
    
  {
    //@ open LocalClass_desugared$1InnerClass_state(this, x);
    
    return this.x;
  }
    
  void setX(int i)    
  //@ requires LocalClass_desugared$1InnerClass_state(this, _);
  //@ ensures LocalClass_desugared$1InnerClass_state(this, i);
    
    
  {
    //@ open LocalClass_desugared$1InnerClass_state(this, _);
    x = i;
    //@ close LocalClass_desugared$1InnerClass_state(this, i);
  }
}