/*@ predicate main_pre() = true; @*/

public class Assert_desugared
{
  //@ requires main_pre();
  //@ ensures true;
  public static void main(String[] args)
  {
    int i = 99;
    assert (i > 0);
    assert i > 0;
    char c = 'a';
    assert (c + 4 == 'e');
    assert c + 4 == 'e';
  }
}