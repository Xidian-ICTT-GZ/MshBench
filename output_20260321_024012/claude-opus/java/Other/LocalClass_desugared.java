public class LocalClass_desugared
{
  //@ requires true;
  //@ ensures true;
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
  
  //@ requires true;
  //@ ensures this.x == 1;
  LocalClass_desugared$1InnerClass()    
  {
    super();
  }
  
  //@ requires true;
  //@ ensures result == this.x;
  int getX()    
  {
    return this.x;
  }
  
  //@ requires true;
  //@ ensures this.x == i;
  void setX(int i)    
  {
    x = i;
  }
}