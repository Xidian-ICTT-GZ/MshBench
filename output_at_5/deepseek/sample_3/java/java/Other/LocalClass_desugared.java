public class LocalClass_desugared
{
  public static void main(String[] args)
    
    
  {
    LocalClass_desugared$1InnerClass first = new LocalClass_desugared$1InnerClass();
    first.setX(111);
    int i = first.getX();
    
  }
}

class LocalClass_desugared$1InnerClass 
{
  
  
  int x = 1;
    
  LocalClass_desugared$1InnerClass()    
    
    
  {
    super();
    
  }
    
  int getX()    
    
    
  {
    
    return this.x;
  }
    
  void setX(int i)    
    
    
  {
    x = i;
  }
}