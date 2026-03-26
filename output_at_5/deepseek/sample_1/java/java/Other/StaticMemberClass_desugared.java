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
    
    
  {
    
  }
    
  int getX()    
  //@ requires OuterClass$InnerClass_iclass(this) &*& iclass_x(this, ?v);
  //@ ensures OuterClass$InnerClass_iclass(this) &*& iclass_x(this, v) &*& result == v;
  {
    
    return this.x;
  }
    
  void setX(int i)    
  //@ requires OuterClass$InnerClass_iclass(this) &*& iclass_x(this, _);
  //@ ensures OuterClass$InnerClass_iclass(this) &*& iclass_x(this, i);
  {
    x = i;
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
predicate OuterClass$InnerClass_iclass(OuterClass$InnerClass c) = c.x |-> ?x &*& x >= 0;
predicate iclass_x(OuterClass$InnerClass c, int v) = c.x |-> v;
predicate iclass_y(int v) = OuterClass$InnerClass.y |-> v;
@*/