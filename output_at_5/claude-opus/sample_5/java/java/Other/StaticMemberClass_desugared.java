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

  //@ predicate outerClassInnerClassInv() = this.x |-> x;

  OuterClass$InnerClass()
  //@ requires true;
  //@ ensures outerClassInnerClassInv();
  {
    //@ close outerClassInnerClassInv();
  }
    
  int getX()    
  //@ requires outerClassInnerClassInv();
  //@ ensures outerClassInnerClassInv() &*& result == x;
  {
    //@ open outerClassInnerClassInv();
    return this.x;
  }
    
  void setX(int i)    
  //@ requires outerClassInnerClassInv();
  //@ ensures outerClassInnerClassInv();
  {
    //@ open outerClassInnerClassInv();
    x = i;
    //@ close outerClassInnerClassInv();
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