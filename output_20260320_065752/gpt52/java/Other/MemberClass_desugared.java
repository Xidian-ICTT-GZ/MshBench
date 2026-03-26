class OuterClass 
{
  /*@
  predicate valid() = true;
  @*/
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
  predicate valid(OuterClass o, int xv) = this.this$0 |-> o &*& this.x |-> xv;
  @*/
    
  //@ requires this$0 != null;
  //@ ensures this.valid(this$0, 1);
  OuterClass$InnerClass(OuterClass this$0)    
    
    
  {
    super();
    this.this$0 = this$0;
    
  }

  //@ requires this.valid(?o, ?xv);
  //@ ensures this.valid(o, xv) &*& result == xv;
  int getX()    
    
    
  {
     
    return this.x;
  }
    
  //@ requires this.valid(?o, ?xv);
  //@ ensures this.valid(o, i);
  void setX(int i)    
    
    
  {
    x = i;
  }
}