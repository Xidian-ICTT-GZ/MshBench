public class LocalClass_desugared
{
  //@ requires true;
  //@ ensures true;
  public static void main(String[] args)
    
    
  {
    LocalClass_desugared$1InnerClass first = new LocalClass_desugared$1InnerClass();
    //@ close LocalClass_desugared$1InnerClass_state(first, 1);
    first.setX(111);
    int i = first.getX();
    //@ open LocalClass_desugared$1InnerClass_state(first, i);
    
  }
}

/*@
predicate LocalClass_desugared$1InnerClass_state(LocalClass_desugared$1InnerClass o; int xv) =
  o.x |-> xv;
@*/

class LocalClass_desugared$1InnerClass 
{
  
  
  int x = 1;
    
  //@ requires true;
  //@ ensures true;
  LocalClass_desugared$1InnerClass()    
    
    
  {
    super();
    
  }
    
  //@ requires LocalClass_desugared$1InnerClass_state(this, ?xv);
  //@ ensures LocalClass_desugared$1InnerClass_state(this, xv) &*& result == xv;
  int getX()    
    
    
  {
    
    return this.x;
  }
    
  //@ requires LocalClass_desugared$1InnerClass_state(this, _);
  //@ ensures LocalClass_desugared$1InnerClass_state(this, i);
  void setX(int i)    
    
    
  {
    //@ open LocalClass_desugared$1InnerClass_state(this, _);
    x = i;
    //@ close LocalClass_desugared$1InnerClass_state(this, i);
  }
}