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
  /*@ predicate state(int vx) =
        this.x |-> vx;
  @*/
  
  int x = 1;
  static int y = 1;

  OuterClass$InnerClass()
  //@ requires true;
  //@ ensures state(1);
  {
  }
    
  int getX()    
  //@ requires state(?vx);
  //@ ensures state(vx) &*& result == vx;
  {
    return this.x;
  }
    
  void setX(int i)    
  //@ requires state(_);
  //@ ensures state(i);
  {
    x = i;
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