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

/*@ predicate InnerClass(OuterClass$InnerClass inner, OuterClass outer, int x) = 
      inner.this$0 |-> outer &*& inner.x |-> x;
@*/

class OuterClass$InnerClass 
{
  final OuterClass this$0;
  
  
  
  int x = 1;
    
  //@ requires true;
  //@ ensures InnerClass(this, this$0, 1);
  OuterClass$InnerClass(OuterClass this$0)    
    
    
  {
    super();
    this.this$0 = this$0;
    
  }

  //@ requires InnerClass(this, ?outer, ?x);
  //@ ensures InnerClass(this, outer, x) &*& result == x;
  int getX()    
    
    
  {
     
    return this.x;
  }
    
  //@ requires InnerClass(this, ?outer, ?old_x);
  //@ ensures InnerClass(this, outer, i);
  void setX(int i)    
    
    
  {
    x = i;
  }
}