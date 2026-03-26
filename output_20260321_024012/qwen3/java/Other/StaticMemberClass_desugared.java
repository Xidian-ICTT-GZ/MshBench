class OuterClass 
{
}

public class StaticMemberClass_desugared
{   
  public static void main(String[] args)    
    
    
  {
    //@ predicate InnerClass(OuterClass$InnerClass o; int x_val) = o.x |-> x_val;
    
    OuterClass$InnerClass first = new OuterClass$InnerClass();
    OuterClass$InnerClass second = new OuterClass$InnerClass();
    //@ close InnerClass(first, 1);
    //@ close InnerClass(second, 1);
    first.setX(111);
    //@ open InnerClass(first, _);
    //@ close InnerClass(first, 111);
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
    
  //@ requires InnerClass(this, ?x_val);
  //@ ensures result == x_val;
  int getX()    
    
    
  {
    
    return this.x;
  }
    
  //@ requires InnerClass(this, ?old_x);
  //@ ensures InnerClass(this, i);
  void setX(int i)    
    
    
  {
    //@ open InnerClass(this, old_x);
    x = i;
    //@ close InnerClass(this, i);
  }
    
  static int getY()    
   
   
  {
    return y;
  }
    
  static void setY(int i)    
    
    
  {
    y = i;
  }
}