public interface Inter
{
  /*@
  predicate valid();
  @*/
  
  //@ requires valid();
  //@ ensures valid();
  public int increment(int i);
    
}