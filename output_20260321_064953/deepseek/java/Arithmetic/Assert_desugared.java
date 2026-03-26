public class Assert_desugared
{
  //@ predicate pre() = true;
  //@ predicate post() = true;

  public static void main(String[] args)
  //@ requires pre();
  //@ ensures post();
    
  {
    //@ open pre();
    int i = 99;
    //@ assert i == 99;
    //@ close post();
    assert (i > 0);
    //@ close post();
    assert i > 0;
    char c = 'a';
    //@ assert c == 'a';
    //@ close post();
    assert (c + 4 == 'e');
    //@ close post();
    assert c + 4 == 'e';
    //@ close post();
  }
}