class OuterClass 
{
}

public class StaticMemberClass_desugared
{   
  public static void main(String[] args)    
  //@ requires true;
  //@ ensures true;
  {
    //@ close OuterClass$InnerClass_iclass();
    OuterClass$InnerClass first = new OuterClass$InnerClass();
    //@ close OuterClass$InnerClass_iclass();
    OuterClass$InnerClass second = new OuterClass$InnerClass();
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
  //@ requires OuterClass$InnerClass_iclass();
  //@ ensures OuterClass$InnerClass(this, 1);
  {
    //@ close OuterClass$InnerClass(this, 1);
  }
    
  int getX()    
  //@ requires OuterClass$InnerClass(this, ?v);
  //@ ensures OuterClass$InnerClass(this, v) &*& result == v;
  {
    return this.x;
  }
    
  void setX(int i)    
  //@ requires OuterClass$InnerClass(this, _);
  //@ ensures OuterClass$InnerClass(this, i);
  {
    //@ open OuterClass$InnerClass(this, _);
    x = i;
    //@ close OuterClass$InnerClass(this, i);
  }
    
  static int getY()    
  //@ requires OuterClass$InnerClass_y(?vy);
  //@ ensures OuterClass$InnerClass_y(vy) &*& result == vy;
  {
    return y;
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

/*@
predicate OuterClass$InnerClass_iclass() = true;
predicate OuterClass$InnerClass(OuterClass$InnerClass c, int v) = c.x |-> v;
predicate OuterClass$InnerClass_y(int v) = OuterClass$InnerClass.y |-> v;
@*/