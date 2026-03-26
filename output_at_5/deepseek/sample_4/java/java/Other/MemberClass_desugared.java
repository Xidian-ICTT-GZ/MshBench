class OuterClass 
{
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
    
  OuterClass$InnerClass(OuterClass this$0)    
  //@ requires true;
  //@ ensures OuterClass$InnerClass_pred(this, this$0, 1);
  {
    super();
    this.this$0 = this$0;
    //@ close OuterClass$InnerClass_pred(this, this$0, 1);
  }

  int getX()    
  //@ requires OuterClass$InnerClass_pred(this, ?outer, ?v);
  //@ ensures OuterClass$InnerClass_pred(this, outer, v) &*& result == v;
  {
    //@ open OuterClass$InnerClass_pred(this, outer, v);
    int result = this.x;
    //@ close OuterClass$InnerClass_pred(this, outer, v);
    return result;
  }
    
  void setX(int i)    
  //@ requires OuterClass$InnerClass_pred(this, ?outer, _);
  //@ ensures OuterClass$InnerClass_pred(this, outer, i);
  {
    //@ open OuterClass$InnerClass_pred(this, outer, _);
    x = i;
    //@ close OuterClass$InnerClass_pred(this, outer, i);
  }
}

/*@
predicate OuterClass$InnerClass_pred(OuterClass$InnerClass inner, OuterClass outer, int x) =
    inner.this$0 |-> outer &*& inner.x |-> x;
@*/