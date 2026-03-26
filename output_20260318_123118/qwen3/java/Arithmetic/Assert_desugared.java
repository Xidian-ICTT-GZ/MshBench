//@ predicate char_plus_four(char c; char result) = result == (char)(c + 4);

public class Assert_desugared
{
  //@ requires true;
  //@ ensures true;
  public static void main(String[] args)
  {
    int i = 99;
    //@ assert i > 0;
    //@ assert i > 0;
    char c = 'a';
    //@ assert char_plus_four(c, 'e');
    //@ assert char_plus_four(c, 'e');
  }
}