class OuterClass 
{
}

/*@
predicate OuterClass$InnerClass_inv(OuterClass$InnerClass this) = this.x |-> ?x;
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

  //@ requires true;
  //@ ensures OuterClass$InnerClass_inv(this);
  OuterClass$InnerClass()
  {
  }
    
  //@ requires OuterClass$InnerClass_inv(this);
  //@ ensures OuterClass$InnerClass_inv(this) &*& result == this.x;
  int getX()    
  {
    return this.x;
  }
    
  //@ requires OuterClass$InnerClass_inv(this);
  //@ ensures OuterClass$InnerClass_inv(this);
  void setX(int i)    
  {
    x = i;
  }
    
  //@ requires true;
  //@ ensures result == y;
  static int getY()    
  {
    return y;
  }
    
  //@ requires true;
  //@ ensures true;
  static void setY(int i)    
  {
    y = i;
  }
}