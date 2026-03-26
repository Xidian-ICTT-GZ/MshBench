class OuterClass 
{
}

/*@ 
predicate OuterClass$InnerClass_obj(OuterClass$InnerClass obj, int x_val) = 
  obj.x |-> x_val &*& true;
predicate OuterClass$InnerClass_static(int y_val) = 
  OuterClass$InnerClass.y |-> y_val &*& true;
@*/

public class StaticMemberClass_desugared
{   
  //@ requires OuterClass$InnerClass_static(?y_val);
  //@ ensures OuterClass$InnerClass_static(y_val);
  public static void main(String[] args)    
  {   
    //@ open OuterClass$InnerClass_static(?y_val);
    OuterClass$InnerClass first = new OuterClass$InnerClass();
    OuterClass$InnerClass second = new OuterClass$InnerClass();
    //@ close OuterClass$InnerClass_obj(first, 1);
    //@ close OuterClass$InnerClass_obj(second, 1);

    first.setX(111);
    //@ open OuterClass$InnerClass_obj(first, _);
    int i = first.getX();
    //@ assert i == 111;
    //@ close OuterClass$InnerClass_obj(first, i);

    first.setY(222);
    //@ open OuterClass$InnerClass_static(_);
    int j = second.getY();
    //@ assert j == 222;
    //@ close OuterClass$InnerClass_static(j);
  }
}

class OuterClass$InnerClass 
{  
  int x = 1;
  static int y = 1;

  /*@
  predicate this_(OuterClass$InnerClass obj, int x_val) = 
    obj.x |-> x_val;
  @*/

  OuterClass$InnerClass()
    //@ requires true;
    //@ ensures this_(this, 1);
  {
  }

  int getX()    
    //@ requires this_((this), ?x_val);
    //@ ensures this_(this, x_val) &*& result == x_val;
  {
    return this.x;
  }

  void setX(int i)    
    //@ requires this_(this, ?_x);
    //@ ensures this_(this, i);
  {
    x = i;
  }

  static int getY()    
    //@ requires OuterClass$InnerClass.y |-> ?y_val;
    //@ ensures OuterClass$InnerClass.y |-> y_val &*& result == y_val;
  {
    return y;
  }

  static void setY(int i)    
    //@ requires OuterClass$InnerClass.y |-> ?_;
    //@ ensures OuterClass$InnerClass.y |-> i;
  {
    y = i;
  }
}