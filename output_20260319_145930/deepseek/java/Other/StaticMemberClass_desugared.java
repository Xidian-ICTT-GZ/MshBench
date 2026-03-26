class OuterClass 
{
}

public class StaticMemberClass_desugared
{   
  public static void main(String[] args)    
  //@ requires true;
  //@ ensures true;
  {
    //@ close OuterClass$InnerClass_pred(first);
    OuterClass$InnerClass first = new OuterClass$InnerClass();
    //@ close OuterClass$InnerClass_pred(second);
    OuterClass$InnerClass second = new OuterClass$InnerClass();
    //@ open OuterClass$InnerClass_pred(first);
    first.setX(111);
    //@ close OuterClass$InnerClass_pred(first);
    //@ open OuterClass$InnerClass_pred(first);
    int i = first.getX();
    //@ close OuterClass$InnerClass_pred(first);

    //@ open OuterClass$InnerClass_static_pred();
    first.setY(222);
    //@ close OuterClass$InnerClass_static_pred();
    //@ open OuterClass$InnerClass_static_pred();
    int j = second.getY();
    //@ close OuterClass$InnerClass_static_pred();
  }
}
class OuterClass$InnerClass 
{  
  int x = 1;
  static int y = 1;

  OuterClass$InnerClass()
  //@ requires true;
  //@ ensures OuterClass$InnerClass_pred(this);
  {
  }
    
  int getX()    
  //@ requires OuterClass$InnerClass_pred(this);
  //@ ensures OuterClass$InnerClass_pred(this) &*& result == this.x;
  {
    //@ open OuterClass$InnerClass_pred(this);
    return this.x;
    //@ close OuterClass$InnerClass_pred(this);
  }
    
  void setX(int i)    
  //@ requires OuterClass$InnerClass_pred(this);
  //@ ensures OuterClass$InnerClass_pred(this) &*& this.x == i;
  {
    //@ open OuterClass$InnerClass_pred(this);
    x = i;
    //@ close OuterClass$InnerClass_pred(this);
  }
    
  static int getY()    
  //@ requires OuterClass$InnerClass_static_pred();
  //@ ensures OuterClass$InnerClass_static_pred() &*& result == y;
  {
    //@ open OuterClass$InnerClass_static_pred();
    return y;
    //@ close OuterClass$InnerClass_static_pred();
  }
    
  static void setY(int i)    
  //@ requires OuterClass$InnerClass_static_pred();
  //@ ensures OuterClass$InnerClass_static_pred() &*& y == i;
  {
    //@ open OuterClass$InnerClass_static_pred();
    y = i;
    //@ close OuterClass$InnerClass_static_pred();
  }
}

/*@
predicate OuterClass$InnerClass_pred(OuterClass$InnerClass c) = 
    c.x |-> ?x;
    
predicate OuterClass$InnerClass_static_pred() = 
    OuterClass$InnerClass.y |-> ?y;
@*/