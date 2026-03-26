public class LocalClass_desugared
{
  public static void main(String[] args)
    
    
  {
    //@ predicate InnerClass(LocalClass_desugared$1InnerClass obj; int val) = obj.x |-> val;
    LocalClass_desugared$1InnerClass first = new LocalClass_desugared$1InnerClass();
    //@ close InnerClass(first, 1);
    first.setX(111);
    //@ open InnerClass(first, _);
    //@ close InnerClass(first, 111);
    int i = first.getX();
    //@ open InnerClass(first, _);
    
  }
}

class LocalClass_desugared$1InnerClass 
{
  
  
  int x = 1;
    
  LocalClass_desugared$1InnerClass()    
    
    
  {
    super();
    
  }
    
  /*@
  predicate InnerClass(int val) = this.x |-> val;
  @*/
  //@ requires true;
  //@ ensures InnerClass(result);
  int getX()    
    
    
  {
    //@ open InnerClass(_);
    //@ close InnerClass(this.x);
    return this.x;
  }
    
  //@ requires InnerClass(_);
  //@ ensures InnerClass(i);
  void setX(int i)    
    
    
  {
    //@ open InnerClass(_);
    x = i;
    //@ close InnerClass(i);
  }
}