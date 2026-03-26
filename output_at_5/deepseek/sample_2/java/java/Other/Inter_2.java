public interface Inter
{
  //@ predicate valid();
  //@ requires valid();
  //@ ensures valid() &*& result == i + 1;
  public int increment(int i);
    
    
}