public interface Inter
{
  //@ public model pure boolean validIncrement(int i);
  //@ requires validIncrement(i);
  //@ ensures validIncrement(result);
  public int increment(int i);
    
    
}