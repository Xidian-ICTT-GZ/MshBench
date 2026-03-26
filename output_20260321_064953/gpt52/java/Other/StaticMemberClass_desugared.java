class OuterClass 
{
}

public class StaticMemberClass_desugared
{   
  public static void main(String[] args)    
  //@ requires true;
  //@ ensures true;
  {
    OuterClass$InnerClass first = new OuterClass$InnerClass();
    OuterClass$InnerClass second = new OuterClass$InnerClass();
    first.setX(111);
    int i = first.getX();
    

    first.setY(222);
    int j = second.getY();
    
  }
}
class OuterClass$InnerClass 
{  
  /*@
  predicate valid() = this.x |-> ?vx;
  @*/
  
  int x = 1;
  static int y = 1;

  OuterClass$InnerClass()
  //@ requires true;
  //@ ensures valid();
  {
    //@ close valid();
  }
    
  int getX()    
  //@ requires valid();
  //@ ensures valid() &*& result == this.x;
  {
    //@ open valid();
    int r = this.x;
    //@ close valid();
    return r;
  }
    
  void setX(int i)    
  //@ requires valid();
  //@ ensures valid();
  {
    //@ open valid();
    x = i;
    //@ close valid();
  }
    
  static int getY()    
  //@ requires true;
  //@ ensures true;
  {
    return y;
  }
    
  static void setY(int i)    
  //@ requires true;
  //@ ensures true;
  {
    y = i;
  }
}