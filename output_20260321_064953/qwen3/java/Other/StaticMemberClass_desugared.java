class OuterClass 
{
}

public class StaticMemberClass_desugared
{   
  public static void main(String[] args)    
    
    
  {
    //@ predicate_class OuterClass$InnerClass(OuterClass$InnerClass o; int x_val) = o.x |-> x_val;
    
    
    OuterClass$InnerClass first = new OuterClass$InnerClass();
    //@ close OuterClass$InnerClass(first, 1);
    OuterClass$InnerClass second = new OuterClass$InnerClass();
    //@ close OuterClass$InnerClass(second, 1);
    first.setX(111);
    //@ open OuterClass$InnerClass(first, _);
    //@ close OuterClass$InnerClass(first, 111);
    int i = first.getX();
    

    first.setY(222);
    int j = second.getY();
    
  }
}
class OuterClass$InnerClass 
{  
  
  
  int x = 1;
  static int y = 1;

  OuterClass$InnerClass()
    
    
  {
    
  }
    
  /*@
  predicate instance(OuterClass$InnerClass this; int x_val) = this.x |-> x_val;
  @*/
  int getX()    
    
    
  {
    //@ open instance(this, _);
    //@ close instance(this, this.x);
    return this.x;
  }
    
  void setX(int i)    
    
    
  {
    //@ open instance(this, _);
    x = i;
    //@ close instance(this, i);
  }
    
  static int getY()    
   
   
  {
    return y;
  }
    
  static void setY(int i)    
    
    
  {
    y = i;
  }
}