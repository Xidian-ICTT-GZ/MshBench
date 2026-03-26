public interface Inter
{
  //@ predicate valid() = true;
  
  public int increment(int i);
  //@ requires valid();
  //@ ensures valid();
    
    
}