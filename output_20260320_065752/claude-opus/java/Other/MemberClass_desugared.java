class OuterClass 
{
}

/*@
predicate OuterClass$InnerClass_inv(OuterClass$InnerClass this) =
  this.x |-> _;
@*/
public class MemberClass_desugared
{
  public static void main(String[] args)    
  //@ requires true;
  //@ ensures true;
  {
    OuterClass first = new OuterClass();
    OuterClass$InnerClass second = new OuterClass$InnerClass(first );
    second.setX(111);
    int i = second.getX();
  }
}

class OuterClass$InnerClass 
{
  final OuterClass this$0;
  
  int x = 1;
  
  OuterClass$InnerClass(OuterClass this$0)    
  //@ requires true;
  //@ ensures OuterClass$InnerClass_inv(this);
  {
    super();
    this.this$0 = this$0;
    x = 1;
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
    x = i;
  }
}