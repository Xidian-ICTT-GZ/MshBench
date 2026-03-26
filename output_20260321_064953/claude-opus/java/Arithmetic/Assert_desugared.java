public class Assert_desugared
{
  /*@
  predicate main_pred() = true;
  @*/

  public static void main(String[] args)
  //@ requires main_pred();
  //@ ensures main_pred();
  {
    int i = 99;
    assert (i > 0);
    assert i > 0;
    char c = 'a';
    assert (c + 4 == 'e');
    assert c + 4 == 'e';
  }
}