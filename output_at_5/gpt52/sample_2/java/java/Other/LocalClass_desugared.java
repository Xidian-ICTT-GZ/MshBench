public class LocalClass_desugared
{
  public static void main(String[] args)
  //@ requires true;
  //@ ensures true;
    
    
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
  //@ requires true;
  //@ ensures true;
    
    
  {
    super();
    
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
}