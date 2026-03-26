public interface Inter
{
  //@ public model int input;
  //@ public model int output;

  //@ requires true;
  //@ ensures result == i + 1;
  public int increment(int i);
  
}