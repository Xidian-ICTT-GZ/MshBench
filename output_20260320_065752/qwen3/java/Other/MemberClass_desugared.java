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
    OuterClass$InnerClass second = new OuterClass$InnerClass(first );
    second.setX(111);
    int i = second.getX();
    
  }
}

class OuterClass$InnerClass 
{
  final OuterClass this$0;
  
  
  
  int x = 1;
    
  /*@
  predicate InnerClass_pred(OuterClass outer, int val) =
    this$0 |-> outer &*& x |-> val;
  @*/
    
  //@ requires true;
  //@ ensures InnerClass_pred(this$0, 1);
  OuterClass$InnerClass(OuterClass this$0)    
    
    
  {
    super();
    this.this$0 = this$0;
    
  }

  //@ requires InnerClass_pred(?outer, ?val);
  //@ ensures InnerClass_pred(outer, val) &*& result == val;
  int getX()    
    
    
  {
     
    return this.x;
  }
    
  //@ requires InnerClass_pred(?outer, ?old_val);
  //@ ensures InnerClass_pred(outer, i);
  void setX(int i)    
    
    
  {
    //@ open InnerClass_pred(_, _);
    x = i;
    //@ close InnerClass_pred(this$0, i);
  }
}