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
  /*@
  predicate OuterClass$InnerClass_state(OuterClass$InnerClass o; int x0) =
    o.x |-> x0;
  @*/
  
  
  int x = 1;
  static int y = 1;

  //@ requires true;
  //@ ensures OuterClass$InnerClass_state(this, 1);
  OuterClass$InnerClass()
    
    
  {
    //@ close OuterClass$InnerClass_state(this, 1);
  }
    
  //@ requires OuterClass$InnerClass_state(this, ?x0);
  //@ ensures OuterClass$InnerClass_state(this, x0) &*& result == x0;
  int getX()    
    
    
  {
    //@ open OuterClass$InnerClass_state(this, x0);
    int r = this.x;
    //@ close OuterClass$InnerClass_state(this, x0);
    return r;
  }
    
  //@ requires OuterClass$InnerClass_state(this, ?x0);
  //@ ensures OuterClass$InnerClass_state(this, i);
  void setX(int i)    
    
    
  {
    //@ open OuterClass$InnerClass_state(this, x0);
    x = i;
    //@ close OuterClass$InnerClass_state(this, i);
  }
    
  //@ requires true;
  //@ ensures true;
  static int getY()    
   
   
  {
    return y;
  }
    
  //@ requires true;
  //@ ensures true;
  static void setY(int i)    
    
    
  {
    y = i;
  }
}