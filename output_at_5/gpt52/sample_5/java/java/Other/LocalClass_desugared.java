public class LocalClass_desugared
{
  public static void main(String[] args)
  //@ requires true;
  //@ ensures true;
    
    
  {
    LocalClass_desugared$1InnerClass first = new LocalClass_desugared$1InnerClass();
    first.setX(111);
    int i = first.getX();
    
  }
}

class LocalClass_desugared$1InnerClass 
{
  /*@
  predicate valid(int v) = this.x |-> v;
  @*/
  
  
  int x = 1;
    
  LocalClass_desugared$1InnerClass()    
  //@ requires true;
  //@ ensures valid(1);
    
    
  {
    super();
    //@ close valid(1);
    
  }
    
  int getX()    
  //@ requires valid(?v);
  //@ ensures valid(v) &*& result == v;
    
    
  {
    //@ open valid(v);
    int r = this.x;
    //@ close valid(v);
    return r;
  }
    
  void setX(int i)    
  //@ requires valid(?v);
  //@ ensures valid(i);
    
    
  {
    //@ open valid(v);
    x = i;
    //@ close valid(i);
  }
}