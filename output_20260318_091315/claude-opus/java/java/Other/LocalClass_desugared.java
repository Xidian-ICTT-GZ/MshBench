public class LocalClass_desugared
{
  //@ predicate main_inv() = true;
  public static void main(String[] args)
    //@ requires main_inv();
    //@ ensures  main_inv();
  {
    LocalClass_desugared$1InnerClass first = new LocalClass_desugared$1InnerClass();
    first.setX(111);
    int i = first.getX();
  }
}

class LocalClass_desugared$1InnerClass 
{
  int x = 1;
  //@ predicate thisInv() = this.x |-> _;
    
  LocalClass_desugared$1InnerClass()    
    //@ requires true;
    //@ ensures thisInv();
  {
    super();
  }
    
  int getX()    
    //@ requires thisInv();
    //@ ensures thisInv() &*& result == x;
  {
    return this.x;
  }
    
  void setX(int i)    
    //@ requires thisInv();
    //@ ensures thisInv() &*& x == i;
  {
    x = i;
  }
}