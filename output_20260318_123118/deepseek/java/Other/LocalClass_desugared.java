public class LocalClass_desugared
{
  //@ predicate InnerClass(InnerClass i;) = i.x |-> ?v;
  
  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
  {
    //@ close InnerClassPred();
    LocalClass_desugared$1InnerClass first = new LocalClass_desugared$1InnerClass();
    //@ open InnerClassPred();
    //@ close InnerClass(first);
    first.setX(111);
    //@ open InnerClass(first);
    int i = first.getX();
    //@ close InnerClassPred();
    
  }
  
  //@ predicate InnerClassPred() = true;
}

class LocalClass_desugared$1InnerClass 
{
  
  
  int x = 1;
    
  LocalClass_desugared$1InnerClass()    
    //@ requires LocalClass_desugared.InnerClassPred();
    //@ ensures LocalClass_desugared.InnerClass(this);
    
    
  {
    super();
    
  }
    
  int getX()    
    //@ requires LocalClass_desugared.InnerClass(this) &*& this.x |-> ?v;
    //@ ensures LocalClass_desugared.InnerClass(this) &*& this.x |-> v &*& result == v;
    
    
  {
    
    return this.x;
  }
    
  void setX(int i)    
    //@ requires LocalClass_desugared.InnerClass(this) &*& this.x |-> _;
    //@ ensures LocalClass_desugared.InnerClass(this) &*& this.x |-> i;
    
    
  {
    x = i;
  }
}