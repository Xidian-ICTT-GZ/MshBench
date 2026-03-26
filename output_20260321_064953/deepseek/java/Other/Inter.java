public interface Inter
{
  //@ predicate pre(int i);
  //@ predicate post(int i, int result);
  
  public int increment(int i);
  //@ requires pre(i);
  //@ ensures post(i, result);
    
    
}