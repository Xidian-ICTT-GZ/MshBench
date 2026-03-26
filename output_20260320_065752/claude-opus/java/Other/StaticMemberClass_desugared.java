class OuterClass 
{
}

/*@
predicate OuterClass$InnerClass_inv(OuterClass$InnerClass this) =
  this.x |-> _;
@*/
public class StaticMemberClass_desugared
{   
  public static void main(String[] args)    
  {
    OuterClass$InnerClass first = new OuterClass$InnerClass();
    OuterClass$InnerClass second = new OuterClass$InnerClass();
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

  /*@
  requires true;
  ensures this.x == 1 &*& OuterClass$InnerClass_inv(this);
  @*/
  OuterClass$InnerClass()
  {
    //@ close OuterClass$InnerClass_inv(this);
  }
    
  /*@
  requires OuterClass$InnerClass_inv(this);
  ensures OuterClass$InnerClass_inv(this);
  @*/
  int getX()    
  {
    //@ open OuterClass$InnerClass_inv(this);
    int result = this.x;
    //@ close OuterClass$InnerClass_inv(this);
    return result;
  }
    
  /*@
  requires OuterClass$InnerClass_inv(this);
  ensures OuterClass$InnerClass_inv(this);
  @*/
  void setX(int i)    
  {
    //@ open OuterClass$InnerClass_inv(this);
    x = i;
    //@ close OuterClass$InnerClass_inv(this);
  }
    
  /*@
  requires true;
  ensures true;
  @*/
  static int getY()   
  {
    return y;
  }
    
  /*@
  requires true;
  ensures true;
  @*/
  static void setY(int i)    
  {
    y = i;
  }
}