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

  OuterClass$InnerClass()
    
    
  //@ requires true;
  //@ ensures true;
  {
    
  }
    
  int getX()    
    
    
  //@ requires true;
  //@ ensures true;
  {
    
    return this.x;
  }
    
  void setX(int i)    
    
    
  //@ requires true;
  //@ ensures true;
  {
    x = i;
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