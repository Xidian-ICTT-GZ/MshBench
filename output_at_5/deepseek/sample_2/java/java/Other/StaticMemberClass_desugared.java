class OuterClass 
{
}

public class StaticMemberClass_desugared
{   
  public static void main(String[] args)    
    
    
  {
    
    
    OuterClass$InnerClass first = new OuterClass$InnerClass();
    OuterClass$InnerClass second = new OuterClass$InnerClass();
    //@ close OuterClass$InnerClass_iclass(first);
    //@ close OuterClass$InnerClass_iclass(second);
    first.setX(111);
    int i = first.getX();
    

    first.setY(222);
    int j = second.getY();
    
  }
}
class OuterClass$InnerClass 
{  
  
  
  int x = 1;
  static int y = 1;

  OuterClass$InnerClass()
  //@ ensures OuterClass$InnerClass_iclass(this);
  {
    //@ close OuterClass$InnerClass_iclass(this);
  }
    
  int getX()    
  //@ requires OuterClass$InnerClass_iclass(this);
  //@ ensures OuterClass$InnerClass_iclass(this) &*& result == this.x;
  {
    //@ open OuterClass$InnerClass_iclass(this);
    return this.x;
  }
    
  void setX(int i)    
  //@ requires OuterClass$InnerClass_iclass(this);
  //@ ensures OuterClass$InnerClass_iclass(this);
  {
    //@ open OuterClass$InnerClass_iclass(this);
    x = i;
    //@ close OuterClass$InnerClass_iclass(this);
  }
    
  static int getY()    
  //@ requires iclass_y(?v);
  //@ ensures iclass_y(v) &*& result == v;
  {
    return y;
  }
    
  static void setY(int i)    
  //@ requires iclass_y(_);
  //@ ensures iclass_y(i);
  {
    y = i;
  }
}

/*@
predicate OuterClass$InnerClass_iclass(OuterClass$InnerClass c) = c.x |-> _;
predicate iclass_y(int v) = OuterClass$InnerClass.y |-> v;
@*/