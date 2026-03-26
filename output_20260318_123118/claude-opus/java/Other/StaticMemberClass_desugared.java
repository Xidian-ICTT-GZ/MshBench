class OuterClass 
{
}

/*@ predicate OuterClass$InnerClass_inv(OuterClass$InnerClass o) =
      o.x |-> _; @*/

public class StaticMemberClass_desugared
{   
  //@ requires true;
  //@ ensures true;
  public static void main(String[] args)    
    //@ requires args != null;
    //@ ensures true;
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

  //@ predicate_object_class InnerClassInv() = this.x |-> _;
  /*@ predicate_static_class StaticFieldYInv(int v) = (y |-> v); @*/

  OuterClass$InnerClass()
    //@ requires true;
    //@ ensures OuterClass$InnerClass_inv(this);
  {
  }

  //@ requires OuterClass$InnerClass_inv(this);
  //@ ensures OuterClass$InnerClass_inv(this) &*& result == this.x;
  int getX()    
  {
    return this.x;
  }
    
  //@ requires OuterClass$InnerClass_inv(this);
  //@ ensures OuterClass$InnerClass_inv(this);
  void setX(int i)    
  {
    x = i;
  }

  //@ requires StaticFieldYInv(?v);
  //@ ensures StaticFieldYInv(i) &*& result == v;
  static int getY()    
  {
    return y;
  }

  //@ requires StaticFieldYInv(?_);
  //@ ensures StaticFieldYInv(i);
  static void setY(int i)    
  {
    y = i;
  }
}