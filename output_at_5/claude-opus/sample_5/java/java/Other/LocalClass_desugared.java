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
  int x;
  
  /*@ predicate inv(LocalClass_desugared$1InnerClass this) = this.x |-> ?vx; @*/

  LocalClass_desugared$1InnerClass()    
    //@ requires true;
    //@ ensures inv(this);
  {
    super();
    x = 1;
    //@ close inv(this);
  }
  
  int getX()    
    //@ requires inv(this);
    //@ ensures inv(this) &*& result == x;
  {
    //@ open inv(this);
    int value = x;
    //@ close inv(this);
    return value;
  }
  
  void setX(int i)    
    //@ requires inv(this);
    //@ ensures inv(this);
  {
    //@ open inv(this);
    x = i;
    //@ close inv(this);
  }
}