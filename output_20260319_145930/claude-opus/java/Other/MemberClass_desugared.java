class OuterClass 
{
}

/*@
predicate OuterClass$InnerClass_pred(OuterClass$InnerClass obj; OuterClass outer, int xval) =
    obj.this$0 |-> outer &*& obj.x |-> xval;
@*/

public class MemberClass_desugared
{
  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
  {
    OuterClass first = new OuterClass();
    OuterClass$InnerClass second = new OuterClass$InnerClass(first);
    //@ open OuterClass$InnerClass_pred(second, _, _);
    //@ close OuterClass$InnerClass_pred(second, first, 1);
    second.setX(111);
    int i = second.getX();
    //@ open OuterClass$InnerClass_pred(second, _, _);
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
    //@ requires OuterClass$InnerClass_pred(this, ?outer, ?xval);
    //@ ensures OuterClass$InnerClass_pred(this, outer, xval) &*& result == xval;
  {
    //@ open OuterClass$InnerClass_pred(this, outer, xval);
    int tmp = this.x;
    //@ close OuterClass$InnerClass_pred(this, outer, xval);
    return tmp;
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