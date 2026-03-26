class OuterClass 
{
}

/*@ predicate InnerClass(OuterClass$InnerClass o; int xval) = o.x |-> xval; @*/

public class StaticMemberClass_desugared
{   
  //@ requires true;
  //@ ensures true;
  public static void main(String[] args)    
    
    
  {
    
    
    OuterClass$InnerClass first = new OuterClass$InnerClass();
    OuterClass$InnerClass second = new OuterClass$InnerClass();
    //@ close InnerClass(first, 1);
    //@ close InnerClass(second, 1);
    first.setX(111);
    //@ open InnerClass(first, _);
    //@ close InnerClass(first, 111);
    int i = first.getX();
    //@ assert InnerClass(first, 111);

    first.setY(222);
    int j = second.getY();
    
  }
}
class OuterClass$InnerClass 
{  
  
  
  int x = 1;
  static int y = 1;

  //@ requires true;
  //@ ensures InnerClass(this, 1);
  OuterClass$InnerClass()
    
    
  {
    
  }
    
  //@ requires InnerClass(this, ?xval);
  //@ ensures InnerClass(this, xval) &*& result == xval;
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