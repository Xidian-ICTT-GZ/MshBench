//@ predicate OuterClass$InnerClass(OuterClass$InnerClass o; int x_val) = 
//@   o.x |-> x_val;

/*@ predicate static_y(int y_val) = 
    [?f]OuterClass$InnerClass.y |-> y_val;
@*/

class OuterClass 
{
}

public class StaticMemberClass_desugared
{   
  //@ requires true;
  //@ ensures true;
  public static void main(String[] args)    
  {
    OuterClass$InnerClass first = new OuterClass$InnerClass();
    OuterClass$InnerClass second = new OuterClass$InnerClass();
    //@ close OuterClass$InnerClass(first, 1);
    //@ close OuterClass$InnerClass(second, 1);
    first.setX(111);
    //@ open OuterClass$InnerClass(first, _);
    //@ close OuterClass$InnerClass(first, 111);
    int i = first.getX();
    //@ open OuterClass$InnerClass(first, _);

    first.setY(222);
    //@ close static_y(222);
    int j = second.getY();
    //@ open static_y(_);
  }
}

class OuterClass$InnerClass 
{  
  int x = 1;
  static int y = 1;

  //@ requires true;
  //@ ensures OuterClass$InnerClass(this, 1);
  OuterClass$InnerClass()
  {
  }
    
  //@ requires OuterClass$InnerClass(this, ?x_val);
  //@ ensures OuterClass$InnerClass(this, x_val) &*& result == x_val;
  int getX()    
  {
    return this.x;
  }
    
  //@ requires OuterClass$InnerClass(this, ?old_x);
  //@ ensures OuterClass$InnerClass(this, i);
  void setX(int i)    
  {
    x = i;
  }
    
  //@ requires static_y(?y_val);
  //@ ensures static_y(y_val) &*& result == y_val;
  static int getY()    
  {
    return y;
  }
    
  //@ requires true;
  //@ ensures static_y(i);
  static void setY(int i)    
  {
    y = i;
  }
}