/*@ predicate OuterClass$InnerClass(OuterClass$InnerClass o; int x_val) =
  o.x |-> x_val;
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
    
  //@ requires true;
  //@ ensures result == y;
  static int getY()    
  {
    return y;
  }
    
  //@ requires true;
  //@ ensures y == i;
  static void setY(int i)    
  {
    y = i;
  }
}