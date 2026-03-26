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
  //@ requires this$0 != null;
  //@ ensures OuterClass$InnerClass_x(this, 1) &*& this.this$0 |-> this$0;
  {
    super();
    this.this$0 = this$0;
    
  }

  int getX()    
  //@ requires OuterClass$InnerClass_x(this, ?v);
  //@ ensures OuterClass$InnerClass_x(this, v) &*& result == v;
  {
     
    return this.x;
  }
    
  void setX(int i)    
  //@ requires OuterClass$InnerClass_x(this, _);
  //@ ensures OuterClass$InnerClass_x(this, i);
  {
    x = i;
  }
}

/*@
predicate OuterClass$InnerClass_x(OuterClass$InnerClass i; int v) = i.x |-> v;
@*/