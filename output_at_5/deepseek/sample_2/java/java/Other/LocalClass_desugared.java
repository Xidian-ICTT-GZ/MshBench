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
  //@ ensures InnerClassPred(this.x);
    
    
  {
    super();
    //@ close InnerClassPred(this.x);
  }
    
  int getX()    
  //@ requires InnerClassPred(?v);
  //@ ensures InnerClassPred(v) &*& result == v;
    
  {
    //@ open InnerClassPred(v);
    return this.x;
    //@ close InnerClassPred(v);
  }
    
  void setX(int i)    
  //@ requires InnerClassPred(_);
  //@ ensures InnerClassPred(i);
    
  {
    //@ open InnerClassPred(_);
    x = i;
    //@ close InnerClassPred(i);
  }
  
  /*@
  predicate InnerClassPred(int v) = this.x |-> v;
  @*/
}