/*@ predicate innerClass(LocalClass_desugared$1InnerClass o; int v) =
  o.x |-> v;
@*/

public class LocalClass_desugared
{
  //@ requires true;
  //@ ensures true;
  public static void main(String[] args)
  {
    LocalClass_desugared$1InnerClass first = new LocalClass_desugared$1InnerClass();
    //@ assert innerClass(first, _);
    first.setX(111);
    //@ assert innerClass(first, 111);
    int i = first.getX();
    //@ assert i == 111;
  }
}

class LocalClass_desugared$1InnerClass 
{
  int x = 1;
    
  //@ requires true;
  //@ ensures innerClass(this, 1);
  LocalClass_desugared$1InnerClass()    
  {
    super();
  }
    
  //@ requires innerClass(this, ?v);
  //@ ensures innerClass(this, v) &*& result == v;
  int getX()    
  {
    return this.x;
  }
    
  //@ requires innerClass(this, ?v);
  //@ ensures innerClass(this, i);
  void setX(int i)    
  {
    x = i;
  }
}