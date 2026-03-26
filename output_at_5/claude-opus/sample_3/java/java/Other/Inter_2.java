public interface Inter
{
  /*@
  predicate valid_interface(this) = true;
  @*/

  //@ requires valid_interface(this);
  //@ ensures valid_interface(this);
  public int increment(int i);
    
    
}