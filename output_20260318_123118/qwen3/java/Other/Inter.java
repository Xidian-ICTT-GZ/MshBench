/*@ predicate valid_inter(Inter this) = true; @*/

public interface Inter
{
  //@ requires valid_inter(this);
  //@ ensures result == i + 1;
  public int increment(int i);
}