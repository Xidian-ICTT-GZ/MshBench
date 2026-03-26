class OuterClass 
{
  /*@ predicate outer_class(Object o) = o == this; @*/
}

public class MemberClass_desugared
{
  //@ requires true;
  //@ ensures true;
  public static void main(String[] args)    
  //@ requires args != null &*& args.length >= 0 &*& true;
  //@ ensures true;
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

  //@ predicate inner_class(OuterClass$InnerClass this, OuterClass outer, int value) = this.this$0 |-> outer &*& this.x |-> value;

  //@ requires outer != null;
  //@ ensures inner_class(this, outer, 1);
  OuterClass$InnerClass(OuterClass this$0)    
  {
    super();
    this.this$0 = this$0;
  }

  //@ requires inner_class(this, this$0, ?v);
  //@ ensures inner_class(this, this$0, v) &*& result == v;
  int getX()    
  {
    return this.x;
  }

  //@ requires inner_class(this, this$0, ?v);
  //@ ensures inner_class(this, this$0, i);
  void setX(int i)    
  {
    x = i;
  }
}