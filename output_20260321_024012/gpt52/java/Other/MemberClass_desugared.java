class OuterClass 
{
  /*@
  predicate outer() = true;
  @*/
}

public class MemberClass_desugared
{
  public static void main(String[] args)    
  //@ requires true;
  //@ ensures true;
  {
    

    OuterClass first = new OuterClass();
    //@ close first.outer();
    OuterClass$InnerClass second = new OuterClass$InnerClass(first );
    //@ close second.inner(first);
    //@ open second.inner(first);
    second.setX(111);
    //@ close second.inner(first);
    //@ open second.inner(first);
    int i = second.getX();
    //@ close second.inner(first);
    
  }
}

class OuterClass$InnerClass 
{
  final OuterClass this$0;
  
  
  
  int x = 1;
    
  /*@
  predicate inner(OuterClass outer) =
    this.this$0 |-> outer &*& outer.outer() &*& this.x |-> ?v;
  @*/

  OuterClass$InnerClass(OuterClass this$0)    
  //@ requires this$0 != null &*& this$0.outer();
  //@ ensures this.inner(this$0);
  {
    super();
    this.this$0 = this$0;
    //@ close this.inner(this$0);
    
  }

  int getX()    
  //@ requires this.inner(?outer);
  //@ ensures this.inner(outer) &*& result == ?r;
  {
    //@ open this.inner(?outer);
    int r = this.x;
    //@ close this.inner(outer);
    return r;
  }
    
  void setX(int i)    
  //@ requires this.inner(?outer);
  //@ ensures this.inner(outer);
  {
    //@ open this.inner(?outer);
    x = i;
    //@ close this.inner(outer);
  }
}