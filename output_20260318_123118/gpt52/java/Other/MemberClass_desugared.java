class OuterClass 
{
  /*@ predicate inv() = true; @*/
}

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

  /*@ predicate inv(int v) = this.this$0 |-> ?o &*& this.x |-> v; @*/
    
  OuterClass$InnerClass(OuterClass this$0)    
  //@ requires this$0 != null;
  //@ ensures inv(1);
  {
    super();
    this.this$0 = this$0;
  }

  int getX()    
  //@ requires inv(?v);
  //@ ensures inv(v) &*& result == v;
  {
    return this.x;
  }
    
  void setX(int i)    
  //@ requires inv(?v);
  //@ ensures inv(i);
  {
    x = i;
  }
}