public interface Inter
{
  /*@
  predicate valid();
  @*/
  
  //@ requires valid();
  //@ ensures valid();
  //@ ensures true;
  public int increment(int i);
    
}