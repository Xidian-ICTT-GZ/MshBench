public interface Inter
{
  public int increment(int i)
    //@ requires true;
    //@ ensures result == i + 1;
  ;
}