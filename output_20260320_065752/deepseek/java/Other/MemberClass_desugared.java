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
  //@ ensures OuterClass$InnerClass_pred(this);
  {
    super();
    this.this$0 = this$0;
    //@ close OuterClass$InnerClass_pred(this);
  }

  int getX()    
  //@ requires OuterClass$InnerClass_pred(this);
  //@ ensures OuterClass$InnerClass_pred(this) &*& result == this.x;
  {
    //@ open OuterClass$InnerClass_pred(this);
    return this.x;
    //@ close OuterClass$InnerClass_pred(this);
  }
    
  void setX(int i)    
  //@ requires OuterClass$InnerClass_pred(this);
  //@ ensures OuterClass$InnerClass_pred(this);
  {
    //@ open OuterClass$InnerClass_pred(this);
    x = i;
    //@ close OuterClass$InnerClass_pred(this);
  }
}

/*@
predicate OuterClass$InnerClass_pred(OuterClass$InnerClass this) =
    this.this$0 |-> ?o &*& this.x |-> ?x;
@*/