class OuterClass 
{
}

public class MemberClass_desugared
{
  public static void main(String[] args)    
  {
    OuterClass first = new OuterClass();
    OuterClass$InnerClass second = new OuterClass$InnerClass(first);
    second.setX(111);
    int i = second.getX();
  }
}

class OuterClass$InnerClass 
{
  final OuterClass this$0;
  
  int x = 1;
  
  /*@
  predicate this_inv() = this != null &*& this$0 != null;
  @*/
  
  //@ requires this$0 != null;
  //@ ensures this_inv();
  OuterClass$InnerClass(OuterClass this$0)    
  {
    super();
    this.this$0 = this$0;
  }

  //@ requires this_inv();
  //@ ensures this_inv() &*& result == x;
  int getX()    
  {
    return this.x;
  }
  
  //@ requires this_inv();
  //@ ensures this_inv();
  void setX(int i)    
  {
    x = i;
  }
}