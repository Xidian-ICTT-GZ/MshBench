class OuterClass 
{
}

public class MemberClass_desugared
{
  //@ predicate OuterClass$InnerClass(OuterClass$InnerClass ic;) = ic.x |-> ?v &*& ic.this$0 |-> ?o;
  
  public static void main(String[] args)    
  {
    //@ close true;
    

    OuterClass first = new OuterClass();
    OuterClass$InnerClass second = new OuterClass$InnerClass(first );
    //@ close OuterClass$InnerClass(second);
    second.setX(111);
    //@ open OuterClass$InnerClass(second);
    int i = second.getX();
    //@ assert i == 111;
    //@ open OuterClass$InnerClass(second);
    
  }
}

class OuterClass$InnerClass 
{
  final OuterClass this$0;
  
  
  
  int x = 1;
    
  OuterClass$InnerClass(OuterClass this$0)    
  //@ requires true;
  //@ ensures OuterClass$InnerClass(this);
  {
    super();
    this.this$0 = this$0;
    //@ close OuterClass$InnerClass(this);
    
  }

  int getX()    
  //@ requires OuterClass$InnerClass(this);
  //@ ensures OuterClass$InnerClass(this) &*& result == this.x;
  {
    //@ open OuterClass$InnerClass(this);
    return this.x;
    //@ close OuterClass$InnerClass(this);
  }
    
  void setX(int i)    
  //@ requires OuterClass$InnerClass(this);
  //@ ensures OuterClass$InnerClass(this) &*& this.x == i;
  {
    //@ open OuterClass$InnerClass(this);
    x = i;
    //@ close OuterClass$InnerClass(this);
  }
}