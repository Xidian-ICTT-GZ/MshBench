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
  predicate OuterClass$InnerClass_inv(OuterClass$InnerClass o; int vx) =
    o.x |-> vx;
  @*/
  
  int x = 1;
  static int y = 1;

  OuterClass$InnerClass()
  //@ requires true;
  //@ ensures OuterClass$InnerClass_inv(this, 1);
  {
    
  }
    
  int getX()    
  //@ requires OuterClass$InnerClass_inv(this, ?vx);
  //@ ensures OuterClass$InnerClass_inv(this, vx) &*& result == vx;
  {
    //@ open OuterClass$InnerClass_inv(this, vx);
    int r = this.x;
    //@ close OuterClass$InnerClass_inv(this, vx);
    return r;
  }
    
  void setX(int i)    
  //@ requires OuterClass$InnerClass_inv(this, ?vx);
  //@ ensures OuterClass$InnerClass_inv(this, i);
  {
    //@ open OuterClass$InnerClass_inv(this, vx);
    x = i;
    //@ close OuterClass$InnerClass_inv(this, i);
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