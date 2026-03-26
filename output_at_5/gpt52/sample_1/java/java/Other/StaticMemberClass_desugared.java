class OuterClass 
{
}

public class StaticMemberClass_desugared
{   
  public static void main(String[] args)    
    
    
  //@ requires true;
  //@ ensures true;
  {
    
    
    OuterClass$InnerClass first = new OuterClass$InnerClass();
    OuterClass$InnerClass second = new OuterClass$InnerClass();
    //@ close OuterClass$InnerClass_state(first, 1);
    //@ close OuterClass$InnerClass_state(second, 1);
    first.setX(111);
    int i = first.getX();
    

    OuterClass$InnerClass.setY(222);
    int j = OuterClass$InnerClass.getY();
    
    //@ open OuterClass$InnerClass_state(first, _);
    //@ open OuterClass$InnerClass_state(second, _);
  }
}
class OuterClass$InnerClass 
{  
  /*@
  predicate OuterClass$InnerClass_state(OuterClass$InnerClass o, int xv) =
    o.x |-> xv;
  @*/
  
  
  int x = 1;
  static int y = 1;

  OuterClass$InnerClass()
    
    
  //@ requires true;
  //@ ensures OuterClass$InnerClass_state(this, 1);
  {
    //@ close OuterClass$InnerClass_state(this, 1);
  }
    
  int getX()    
    
    
  //@ requires OuterClass$InnerClass_state(this, ?xv);
  //@ ensures OuterClass$InnerClass_state(this, xv) &*& result == xv;
  {
    //@ open OuterClass$InnerClass_state(this, xv);
    int res = this.x;
    //@ close OuterClass$InnerClass_state(this, xv);
    return res;
  }
    
  void setX(int i)    
    
    
  //@ requires OuterClass$InnerClass_state(this, _);
  //@ ensures OuterClass$InnerClass_state(this, i);
  {
    //@ open OuterClass$InnerClass_state(this, _);
    x = i;
    //@ close OuterClass$InnerClass_state(this, i);
  }
    
  static int getY()    
   
   
  //@ requires true;
  //@ ensures true;
  {
    return y;
  }
    
  static void setY(int i)    
    
    
  //@ requires true;
  //@ ensures true;
  {
    y = i;
  }
}