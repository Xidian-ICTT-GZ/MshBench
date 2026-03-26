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

/*@ predicate OuterClass$InnerClass(OuterClass$InnerClass obj; OuterClass outer, int x) =
      obj.this$0 |-> outer &*& obj.x |-> x;
@*/

class OuterClass$InnerClass 
{
  final OuterClass this$0;
  
  
  
  int x = 1;
    
  //@ requires true;
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
    //@ open OuterClass$InnerClass(this, _, _);
    x = i;
    //@ close OuterClass$InnerClass(this, this.this$0, i);
  }
}