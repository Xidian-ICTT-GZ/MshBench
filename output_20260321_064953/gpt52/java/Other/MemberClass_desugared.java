class OuterClass 
{
  /*@
  predicate outer(OuterClass o) = o != null;
  @*/
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

  /*@
  predicate inner(OuterClass$InnerClass c; OuterClass o, int xv) =
    c != null &*& c.this$0 |-> o &*& c.x |-> xv;
  @*/
    
  OuterClass$InnerClass(OuterClass this$0)    
    
    
  //@ requires true;
  //@ ensures inner(this, this$0, 1);
  {
    super();
    this.this$0 = this$0;
    
  }

  int getX()    
    
    
  //@ requires inner(this, ?o, ?xv);
  //@ ensures inner(this, o, xv) &*& result == xv;
  {
    //@ open inner(this, o, xv);
    int r = this.x;
    //@ close inner(this, o, xv);
    return r;
  }
    
  void setX(int i)    
    
    
  //@ requires inner(this, ?o, ?xv);
  //@ ensures inner(this, o, i);
  {
    //@ open inner(this, o, xv);
    x = i;
    //@ close inner(this, o, i);
  }
}