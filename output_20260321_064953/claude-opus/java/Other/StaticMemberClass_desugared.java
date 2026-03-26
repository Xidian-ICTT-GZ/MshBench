class OuterClass 
{
}

/*@
predicate OuterClass$InnerClass_inv(OuterClass$InnerClass this) = 
  this.x |-> _;
@*/
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
  int x = 1;
  static int y = 1;

  OuterClass$InnerClass()
  //@ requires true;
  //@ ensures OuterClass$InnerClass_inv(this);
  {
  }
    
  int getX()    
  //@ requires OuterClass$InnerClass_inv(this);
  //@ ensures OuterClass$InnerClass_inv(this) &*& result == this.x;
  {
    return this.x;
  }
    
  void setX(int i)    
  //@ requires OuterClass$InnerClass_inv(this);
  //@ ensures OuterClass$InnerClass_inv(this);
  {
    //@ open OuterClass$InnerClass_inv(this);
    x = i;
    //@ close OuterClass$InnerClass_inv(this);
  }
    
  static int getY()    
  //@ requires true;
  //@ ensures true &*& result == y;
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