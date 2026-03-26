class OuterClass 
{
  /*@
  predicate owned() = this != null;
  @*/
}

public class MemberClass_desugared
{
  //@ requires true;
  //@ ensures true;
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
  predicate innerClassPredicate() = 
    this$0 != null &*& this != null;
  @*/
  
  //@ requires this$0 != null;
  //@ ensures innerClassPredicate();
  OuterClass$InnerClass(OuterClass this$0)    
  {
    super();
    this.this$0 = this$0;
  }

  //@ requires innerClassPredicate();
  //@ ensures innerClassPredicate() &*& result == x;
  int getX()    
  {
    return this.x;
  }
  
  //@ requires innerClassPredicate();
  //@ ensures innerClassPredicate();
  void setX(int i)    
  {
    x = i;
  }
}