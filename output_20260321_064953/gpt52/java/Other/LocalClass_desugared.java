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
  predicate inv() = this.x |-> ?v;
  @*/
  
  
  int x = 1;
    
  LocalClass_desugared$1InnerClass()    
  //@ requires true;
  //@ ensures this.inv();    
  {
    super();
    //@ close inv();
    
  }
    
  int getX()    
  //@ requires this.inv();
  //@ ensures this.inv() &*& result == this.x;    
  {
    //@ open inv();
    
    return this.x;
  }
    
  void setX(int i)    
  //@ requires this.inv();
  //@ ensures this.inv();    
  {
    //@ open inv();
    x = i;
    //@ close inv();
  }
}