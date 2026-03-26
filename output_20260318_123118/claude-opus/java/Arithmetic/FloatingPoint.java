class Program {

/*@ predicate MathRandomProper() = true;
  // We define a trivial predicate since Math.random has no specific heap ownership or permissions
  // but we use it to separate the effects hypothetically.
@*/

/*@ ensures result == true || result == false; @*/
public static boolean getRandomBool()
    //@ requires MathRandomProper();
    //@ ensures MathRandomProper() &*& (result == true || result == false);
{
    return Math.random() < 0.5;
}

}