class OuterClass 
{
}

/*@
predicate OuterClass$InnerClass_inv(OuterClass$InnerClass this) = this->x |-> _;
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

  //@ predicate_ctor this.inv() = this->x |-> _;
  OuterClass$InnerClass()
  //@ requires true;
  //@ ensures this.inv();
  {
    //@ close this.inv();
  }
    
  int getX()    
  //@ requires this.inv();
  //@ ensures this.inv() &*& result == this.x;
  {
    //@ open this.inv();
    return this.x;
  }
    
  void setX(int i)    
  //@ requires this.inv();
  //@ ensures this.inv();
  {
    //@ open this.inv();
    x = i;
    //@ close this.inv();
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