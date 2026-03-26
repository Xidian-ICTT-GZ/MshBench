class OuterClass 
{
}

public class MemberClass_desugared
{
  public static void main(String[] args)    
    
    
  {
    

    OuterClass first = new OuterClass();
    //@ close OuterClass$InnerClass_ctor_perm(first);
    OuterClass$InnerClass second = new OuterClass$InnerClass(first );
    //@ open OuterClass$InnerClass_ctor_perm(first);
    second.setX(111);
    int i = second.getX();
    
  }
}

class OuterClass$InnerClass 
{
  final OuterClass this$0;
  
  
  
  int x = 1;
    
  OuterClass$InnerClass(OuterClass this$0)    
    
    
  //@ requires OuterClass$InnerClass_ctor_perm(this$0);
  //@ ensures OuterClass$InnerClass(this, this$0, 1);
  {
    super();
    this.this$0 = this$0;
    
  }

  int getX()    
    
    
  //@ requires OuterClass$InnerClass(this, ?owner, ?v);
  //@ ensures OuterClass$InnerClass(this, owner, v) &*& result == v;
  {
     
    return this.x;
  }
    
  void setX(int i)    
    
    
  //@ requires OuterClass$InnerClass(this, ?owner, _);
  //@ ensures OuterClass$InnerClass(this, owner, i);
  {
    x = i;
  }
}

/*@
predicate OuterClass$InnerClass(OuterClass$InnerClass ic, OuterClass owner, int xv) =
    ic != null &*& ic.this$0 |-> owner &*& ic.x |-> xv &*& owner != null;
@*/

/*@
predicate OuterClass$InnerClass_ctor_perm(OuterClass owner) = true;
@*/