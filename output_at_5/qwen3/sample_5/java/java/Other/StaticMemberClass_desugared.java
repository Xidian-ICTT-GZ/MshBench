public class StaticMemberClass_desugared
{   
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
  
  
  int x = 1;
  static int y = 1;

  OuterClass$InnerClass()
    
    
  {
    
  }
    
  int getX()    
  {
    
    return this.x;
  }
    
  void setX(int i)    
    
    
  {
    x = i;
  }
    
  static int getY()    
   
   
  {
    return y;
  }
    
  static void setY(int i)    
    
    
  {
    y = i;
  }
}