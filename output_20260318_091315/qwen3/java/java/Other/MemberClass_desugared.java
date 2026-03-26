//@ predicate OuterClass$InnerClass(OuterClass$InnerClass o, OuterClass outer, int x) =
//@   o != null &*&
//@   o.this$0 |-> outer &*&
//@   o.x |-> x;

class OuterClass 
{
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
    
  //@ requires this$0 != null;
  //@ ensures OuterClass$InnerClass(this, this$0, 1);
  OuterClass$InnerClass(OuterClass this$0)    
  {
    super();
    this.this$0 = this$0;
  }

  //@ requires OuterClass$InnerClass(this, ?outer, ?x);
  //@ ensures OuterClass$InnerClass(this, outer, x) &*& result == x;
  int getX()    
  {
    return this.x;
  }
    
  //@ requires OuterClass$InnerClass(this, ?outer, ?old_x);
  //@ ensures OuterClass$InnerClass(this, outer, i);
  void setX(int i)    
  {
    x = i;
  }
}