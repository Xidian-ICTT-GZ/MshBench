class OuterClass 
{
  /*@ predicate OuterClass_inv() = true; @*/
}

public class MemberClass_desugared
{
  public static void main(String[] args)    
  //@ requires true;
  //@ ensures true;
  {
    OuterClass first = new OuterClass();
    //@ close first.OuterClass_inv();
    OuterClass$InnerClass second = new OuterClass$InnerClass(first );
    //@ close second.InnerClass_inv();
    second.setX(111);
    int i = second.getX();
    //@ assert i == 111;
    //@ open second.InnerClass_inv();
    //@ open first.OuterClass_inv();
  }
}

class OuterClass$InnerClass 
{
  final OuterClass this$0;
  
  int x = 1;
    
  /*@ predicate InnerClass_inv() =
        this.this$0 |-> ?o &*& o != null &*& o.OuterClass_inv() &*& this.x |-> ?v;
  @*/
  
  OuterClass$InnerClass(OuterClass this$0)    
  //@ requires this$0 != null &*& this$0.OuterClass_inv();
  //@ ensures InnerClass_inv();
  {
    super();
    this.this$0 = this$0;
    //@ close InnerClass_inv();
  }

  int getX()    
  //@ requires InnerClass_inv();
  //@ ensures InnerClass_inv() &*& result == this.x;
  {
    //@ open InnerClass_inv();
    int r = this.x;
    //@ close InnerClass_inv();
    return r;
  }
    
  void setX(int i)    
  //@ requires InnerClass_inv();
  //@ ensures InnerClass_inv();
  {
    //@ open InnerClass_inv();
    x = i;
    //@ close InnerClass_inv();
  }
}