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

/*@
predicate InnerClass_pred(LocalClass_desugared$1InnerClass obj; int x) =
  obj.x |-> x;
@*/

class LocalClass_desugared$1InnerClass 
{
  
  
  int x = 1;
    
  LocalClass_desugared$1InnerClass()    
    //@ requires true;
    //@ ensures InnerClass_pred(this, 1);
  {
    super();
    //@ close InnerClass_pred(this, 1);
  }
    
  int getX()    
    //@ requires InnerClass_pred(this, ?v);
    //@ ensures InnerClass_pred(this, v) &*& result == v;
  {
    //@ open InnerClass_pred(this, v);
    int tmp = this.x;
    //@ close InnerClass_pred(this, v);
    return tmp;
  }
    
  void setX(int i)    
    //@ requires InnerClass_pred(this, _);
    //@ ensures InnerClass_pred(this, i);
  {
    //@ open InnerClass_pred(this, _);
    x = i;
    //@ close InnerClass_pred(this, i);
  }
}