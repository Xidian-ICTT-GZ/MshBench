class Program {

/*@ predicate MathRandom() = true; @*/

public static boolean getRandomBool()
    //@ requires MathRandom();
    //@ ensures MathRandom() &*& (result == true || result == false);
{
    return Math.random() < 0.5;
}

}