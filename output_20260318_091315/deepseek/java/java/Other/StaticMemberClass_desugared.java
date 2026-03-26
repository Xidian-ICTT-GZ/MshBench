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
    //@ requires first != null &*& first.x |-> _;
    //@ ensures first.x |-> 111;
    first.setX(111);
    //@ requires first != null &*& first.x |-> ?v;
    //@ ensures first.x |-> v &*& result == v;
    int i = first.getX();
    

    //@ requires true;
    //@ ensures OuterClass$InnerClass.y |-> 222;
    OuterClass$InnerClass.setY(222);
    //@ requires true &*& OuterClass$InnerClass.y |-> ?v2;
    //@ ensures OuterClass$InnerClass.y |-> v2 &*& result == v2;
    int j = OuterClass$InnerClass.getY();
    
  }
}
class OuterClass$InnerClass 
{  
  
  
  int x = 1;
  static int y = 1;

  //@ requires true;
  //@ ensures this.x |-> 1;
  OuterClass$InnerClass()
    
    
  {
    
  }
    
  //@ requires this != null &*& this.x |-> ?v;
  //@ ensures this.x |-> v &*& result == v;
  int getX()    
    
    
  {
    
    return this.x;
  }
    
  //@ requires this != null &*& this.x |-> _;
  //@ ensures this.x |-> i;
  void setX(int i)    
    
    
  {
    x = i;
  }
    
  //@ requires OuterClass$InnerClass.y |-> ?v;
  //@ ensures OuterClass$InnerClass.y |-> v &*& result == v;
  static int getY()    
   
   
  {
    return y;
  }
    
  //@ requires true;
  //@ ensures OuterClass$InnerClass.y |-> i;
  static void setY(int i)    
    
    
  {
    y = i;
  }
}