class OuterClass 
{
}

/*@
predicate OuterClass$InnerClass_x(OuterClass$InnerClass obj; int v) = obj.x |-> v;
@*/

public class StaticMemberClass_desugared
{   
  public static void main(String[] args)    
    //@ requires OuterClass$InnerClass_y(?yv);
    //@ ensures OuterClass$InnerClass_y(_);
  {
    
    
    OuterClass$InnerClass first = new OuterClass$InnerClass();
    OuterClass$InnerClass second = new OuterClass$InnerClass();
    //@ open OuterClass$InnerClass_x(first, _);
    first.setX(111);
    int i = first.getX();
    //@ close OuterClass$InnerClass_x(first, 111);

    OuterClass$InnerClass.setY(222);
    int j = OuterClass$InnerClass.getY();
    
  }
}

/*@
predicate OuterClass$InnerClass_y(; int v) = OuterClass$InnerClass.y |-> v;
@*/

class OuterClass$InnerClass 
{  
  
  
  int x = 1;
  static int y = 1;

  OuterClass$InnerClass()
    //@ requires true;
    //@ ensures OuterClass$InnerClass_x(this, 1);
  {
    //@ close OuterClass$InnerClass_x(this, 1);
  }
    
  int getX()    
    //@ requires OuterClass$InnerClass_x(this, ?v);
    //@ ensures OuterClass$InnerClass_x(this, v) &*& result == v;
  {
    //@ open OuterClass$InnerClass_x(this, v);
    int tmp = this.x;
    //@ close OuterClass$InnerClass_x(this, v);
    return tmp;
  }
    
  void setX(int i)    
    //@ requires this.x |-> _;
    //@ ensures this.x |-> i;
  {
    x = i;
  }
    
  static int getY()    
    //@ requires OuterClass$InnerClass_y(?v);
    //@ ensures OuterClass$InnerClass_y(v) &*& result == v;
  {
    //@ open OuterClass$InnerClass_y(v);
    int tmp = y;
    //@ close OuterClass$InnerClass_y(v);
    return tmp;
  }
    
  static void setY(int i)    
    //@ requires OuterClass$InnerClass_y(_);
    //@ ensures OuterClass$InnerClass_y(i);
  {
    //@ open OuterClass$InnerClass_y(_);
    y = i;
    //@ close OuterClass$InnerClass_y(i);
  }
}