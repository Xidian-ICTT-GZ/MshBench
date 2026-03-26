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
  predicate valid(int vx) = this.x |-> vx &*& [_]OuterClass$InnerClass_y(_);
  @*/
  
  
  int x = 1;
  static int y = 1;

  OuterClass$InnerClass()
    
    
  //@ requires true;
  //@ ensures valid(1);
  {
    //@ close valid(1);
  }
    
  int getX()    
    
    
  //@ requires valid(?vx);
  //@ ensures valid(vx) &*& result == vx;
  {
    //@ open valid(vx);
    int tmp = this.x;
    //@ close valid(vx);
    return tmp;
  }
    
  void setX(int i)    
    
    
  //@ requires valid(_);
  //@ ensures valid(i);
  {
    //@ open valid(_);
    x = i;
    //@ close valid(i);
  }
    
  static int getY()    
   
   
  //@ requires [_]OuterClass$InnerClass_y(?v);
  //@ ensures [_]OuterClass$InnerClass_y(v) &*& result == v;
  {
    return y;
  }
    
  static void setY(int i)    
    
    
  //@ requires OuterClass$InnerClass_y(_);
  //@ ensures OuterClass$InnerClass_y(i);
  {
    y = i;
  }
}