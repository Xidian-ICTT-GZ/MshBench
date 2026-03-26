class OuterClass 
{
}

public class StaticMemberClass_desugared
{   
  public static void main(String[] args)    
    
    
  {
    //@ close OuterClass$InnerClass_ClassInv();
    //@ close OuterClass$InnerClass_ClassInv();
    
    
    OuterClass$InnerClass first = new OuterClass$InnerClass();
    //@ close OuterClass$InnerClass_InstanceInv(first);
    OuterClass$InnerClass second = new OuterClass$InnerClass();
    //@ close OuterClass$InnerClass_InstanceInv(second);
    first.setX(111);
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
    //@ close InstanceInv(this);
  }
    
  int getX()    
    
    
  {
    //@ open InstanceInv(this);
    return this.x;
    //@ close InstanceInv(this);
  }
    
  void setX(int i)    
    
    
  {
    //@ open InstanceInv(this);
    x = i;
    //@ close InstanceInv(this);
  }
    
  static int getY()    
   
   
  {
    //@ open ClassInv();
    return y;
    //@ close ClassInv();
  }
    
  static void setY(int i)    
    
    
  {
    //@ open ClassInv();
    y = i;
    //@ close ClassInv();
  }
  
  /*@
  predicate InstanceInv(OuterClass$InnerClass this) = this.x |-> _;
  predicate ClassInv() = y |-> _;
  @*/
  
  //@ predicate OuterClass$InnerClass_InstanceInv(OuterClass$InnerClass o) = InstanceInv(o);
  //@ predicate OuterClass$InnerClass_ClassInv() = ClassInv();
}