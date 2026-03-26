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
    //@ requires first != null;
    //@ ensures true;
    first.setX(111);
    //@ requires first != null;
    //@ ensures result == first.x;
    int i = first.getX();
    

    //@ requires true;
    //@ ensures true;
    first.setY(222);
    //@ requires true;
    //@ ensures result == OuterClass$InnerClass.y;
    int j = second.getY();
    
  }
}
class OuterClass$InnerClass 
{  
  
  
  int x = 1;
  static int y = 1;

  //@ requires true;
  //@ ensures this.x == 1 &*& OuterClass$InnerClass.y == 1;
  OuterClass$InnerClass()
    
    
  {
    
  }
    
  //@ requires this != null;
  //@ ensures result == this.x;
  int getX()    
    
    
  {
    
    return this.x;
  }
    
  //@ requires this != null;
  //@ ensures this.x == i;
  void setX(int i)    
    
    
  {
    x = i;
  }
    
  //@ requires true;
  //@ ensures result == OuterClass$InnerClass.y;
  static int getY()    
   
   
  {
    return y;
  }
    
  //@ requires true;
  //@ ensures OuterClass$InnerClass.y == i;
  static void setY(int i)    
    
    
  {
    y = i;
  }
}