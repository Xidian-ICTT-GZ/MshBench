public interface Inter
{
  //@ predicate valid() = true;
  //@ requires valid();
  //@ ensures result == i + 1 &*& valid();
  public int increment(int i);
    
    
}