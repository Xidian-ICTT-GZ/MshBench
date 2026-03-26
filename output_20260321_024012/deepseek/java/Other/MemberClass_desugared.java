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
  //@ ensures this.this$0 |-> this$0 &*& this.x |-> 1;
  {
    super();
    this.this$0 = this$0;
    
  }

  int getX()    
  //@ requires this.x |-> ?v;
  //@ ensures this.x |-> v &*& result == v;
  {
     
    return this.x;
  }
    
  void setX(int i)    
  //@ requires this.x |-> _;
  //@ ensures this.x |-> i;
  {
    x = i;
  }
}