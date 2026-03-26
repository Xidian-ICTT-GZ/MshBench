class OuterClass 
{
  /*@ predicate valid_OuterClass(OuterClass this) = 
    this == this; // trivial ownership predicate for OuterClass objects
  @*/
}

public class MemberClass_desugared
{
  //@ requires true;
  //@ ensures true;
  public static void main(String[] args)    
  {
    OuterClass first = new OuterClass();
    //@ close valid_OuterClass(first);

    OuterClass$InnerClass second = new OuterClass$InnerClass(first);
    //@ close OuterClass$InnerClass.valid_Inner(second, first);

    second.setX(111);
    int i = second.getX();

    //@ open OuterClass$InnerClass.valid_Inner(second, first);
  }
}

class OuterClass$InnerClass 
{
  final OuterClass this$0;
  
  int x = 1;

  /*@ 
  predicate valid_Inner(OuterClass$InnerClass this, OuterClass outer) = 
    this.this$0 |-> outer &*& outer != null &*& 
    outer.valid_OuterClass(outer) &*&
    this.x |-> _; 
  @*/
    
  //@ requires valid_OuterClass(this$0);
  //@ ensures valid_Inner(this, this$0);
  OuterClass$InnerClass(OuterClass this$0)    
  {
    super();
    this.this$0 = this$0;
  }

  //@ requires valid_Inner(this, this.this$0);
  //@ ensures valid_Inner(this, this.this$0) &*& result == this.x;
  int getX()    
  {
    return this.x;
  }
    
  //@ requires valid_Inner(this, this.this$0);
  //@ ensures valid_Inner(this, this.this$0);
  void setX(int i)    
  {
    x = i;
  }
}