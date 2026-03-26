public class Assert_desugared
{
  //@ predicate main_pre() = true;
  //@ predicate main_post() = true;

  public static void main(String[] args)
  //@ requires main_pre();
  //@ ensures main_post();
  {
    int i = 99;
    //@ assert i > 0;
    //@ assert i > 0;
    char c = 'a';
    //@ assert c + 4 == 'e';
    //@ assert c + 4 == 'e';
  }
}