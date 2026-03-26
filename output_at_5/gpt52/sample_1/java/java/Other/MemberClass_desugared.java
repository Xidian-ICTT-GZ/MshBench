class OuterClass 
{
}

public class MemberClass_desugared
{
  //@ requires true;
  //@ ensures true;
  public static void main(String[] args)    
    
    
  {
    

    OuterClass first = new OuterClass();
    OuterClass$InnerClass second = new OuterClass$InnerClass(first );
    second.setX(111);
    int i = second.getX();
    
  }
}

class OuterClass$InnerClass 
{
  final OuterClass this$0;
  
  
  
  int x = 1;
    
  //@ requires true;
  //@ ensures this.this$0 == this$0;
  OuterClass$InnerClass(OuterClass this$0)    
    
    
  {
    super();
    this.this$0 = this$0;
    
  }

  //@ requires true;
  //@ ensures result == this.x;
  int getX()    
    
    
  {
     
    return this.x;
  }
    
  //@ requires true;
  //@ ensures this.x == i;
  void setX(int i)    
    
    
  {
    x = i;
  }
}