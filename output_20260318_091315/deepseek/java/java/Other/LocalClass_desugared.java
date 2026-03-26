public class LocalClass_desugared
{
  //@ predicate LocalClass_desugared$1InnerClass(LocalClass_desugared$1InnerClass this; int x) = this.x |-> x;

  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
  {
    //@ create_local_class$1InnerClass();
    LocalClass_desugared$1InnerClass first = new LocalClass_desugared$1InnerClass();
    //@ close LocalClass_desugared$1InnerClass(first, 1);
    first.setX(111);
    int i = first.getX();
    //@ open LocalClass_desugared$1InnerClass(first, _);
  }
}

class LocalClass_desugared$1InnerClass 
{
  int x = 1;
    
  LocalClass_desugared$1InnerClass()
    //@ requires true;
    //@ ensures LocalClass_desugared.LocalClass_desugared$1InnerClass(this, 1);
  {
    super();
  }
    
  int getX()
    //@ requires LocalClass_desugared.LocalClass_desugared$1InnerClass(this, ?v);
    //@ ensures LocalClass_desugared.LocalClass_desugared$1InnerClass(this, v) &*& result == v;
  {
    //@ open LocalClass_desugared.LocalClass_desugared$1InnerClass(this, v);
    return this.x;
    //@ close LocalClass_desugared.LocalClass_desugared$1InnerClass(this, v);
  }
    
  void setX(int i)
    //@ requires LocalClass_desugared.LocalClass_desugared$1InnerClass(this, _);
    //@ ensures LocalClass_desugared.LocalClass_desugared$1InnerClass(this, i);
  {
    //@ open LocalClass_desugared.LocalClass_desugared$1InnerClass(this, _);
    x = i;
    //@ close LocalClass_desugared.LocalClass_desugared$1InnerClass(this, i);
  }
}