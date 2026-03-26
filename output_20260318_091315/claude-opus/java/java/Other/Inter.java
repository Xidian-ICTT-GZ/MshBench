public interface Inter
{
  //@ requires true;
  //@ ensures result == i + 1;
  public int increment(int i);
}