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

/*@

predicate OuterClass$InnerClass_pred(OuterClass$InnerClass o; int x) =
  o.x |-> x;

@*/

class OuterClass$InnerClass 
{  
  
  
  int x = 1;
  static int y = 1;

  //@ requires true;
  //@ ensures OuterClass$InnerClass_pred(this, 1);
  OuterClass$InnerClass()
    
    
  {
    //@ close OuterClass$InnerClass_pred(this, 1);
  }
    
  //@ requires OuterClass$InnerClass_pred(this, ?x);
  //@ ensures OuterClass$InnerClass_pred(this, x) &*& result == x;
  int getX()    
    
    
  {
    //@ open OuterClass$InnerClass_pred(this, x);
    int r = this.x;
    //@ close OuterClass$InnerClass_pred(this, x);
    return r;
  }
    
  //@ requires OuterClass$InnerClass_pred(this, _);
  //@ ensures OuterClass$InnerClass_pred(this, i);
  void setX(int i)    
    
    
  {
    //@ open OuterClass$InnerClass_pred(this, _);
    x = i;
    //@ close OuterClass$InnerClass_pred(this, i);
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