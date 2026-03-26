class OuterClass 
{
}

public class StaticMemberClass_desugared
{   
  public static void main(String[] args)    
    
    
  {
    //@ predicate_family_instance main_inv(OuterClass$InnerClass o);
    //@ predicate_family_instance main_inv2(OuterClass$InnerClass o);
    
    
    OuterClass$InnerClass first = new OuterClass$InnerClass();
    //@ close main_inv(first);
    OuterClass$InnerClass second = new OuterClass$InnerClass();
    //@ close main_inv2(second);
    first.setX(111);
    //@ open main_inv(first);
    int i = first.getX();
    

    first.setY(222);
    //@ open main_inv2(second);
    int j = second.getY();
    
  }
}
class OuterClass$InnerClass 
{  
  
  
  int x = 1;
  static int y = 1;

  OuterClass$InnerClass()
    
    
  {
    //@ close OuterClass$InnerClass(this);
  }
    
  /*@
  predicate OuterClass$InnerClass(OuterClass$InnerClass this) =
    this.x |-> ?x_val;
  @*/
    
  int getX()    
    
    
  {
    //@ open OuterClass$InnerClass(this);
    //@ close OuterClass$InnerClass(this);
    return this.x;
  }
    
  void setX(int i)    
    
    
  {
    //@ open OuterClass$InnerClass(this);
    x = i;
    //@ close OuterClass$InnerClass(this);
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