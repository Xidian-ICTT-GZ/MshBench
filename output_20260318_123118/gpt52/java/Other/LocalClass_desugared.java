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
  /*@ predicate inv(int v) = this.x |-> v; @*/
  
  int x = 1;
    
  LocalClass_desugared$1InnerClass()    
  //@ requires true;
  //@ ensures inv(1);
  {
    super();
  }
    
  int getX()    
  //@ requires inv(?v);
  //@ ensures inv(v) &*& result == v;
  {
    return this.x;
  }
    
  void setX(int i)    
  //@ requires inv(_);
  //@ ensures inv(i);
  {
    x = i;
  }
}