class OuterClass 
{
}

/*@
predicate outerClassInnerClassInv(OuterClass$InnerClass this) = this.x |-> _;
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

  //@ predicate_ctor outerClassInnerClassInv(this);
  
  OuterClass$InnerClass()
  //@ requires true;
  //@ ensures outerClassInnerClassInv(this);
  {
    //@ close outerClassInnerClassInv(this);
  }
    
  int getX()    
  //@ requires outerClassInnerClassInv(this);
  //@ ensures outerClassInnerClassInv(this) &*& result == x;
  {
    //@ open outerClassInnerClassInv(this);
    return this.x;
  }
    
  void setX(int i)    
  //@ requires outerClassInnerClassInv(this);
  //@ ensures outerClassInnerClassInv(this);
  {
    //@ open outerClassInnerClassInv(this);
    x = i;
    //@ close outerClassInnerClassInv(this);
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