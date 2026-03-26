public interface Inter
{
  /*@
  predicate valid();
  @*/
  
  //@ requires valid();
  //@ ensures valid() &*& result == old(i) + 1;
  public int increment(int i);
    
    
}