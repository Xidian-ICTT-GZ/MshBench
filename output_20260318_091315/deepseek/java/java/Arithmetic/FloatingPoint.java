class Program {

//@ predicate RandomBoolPerm() = true;

public static boolean getRandomBool()
    //@ requires RandomBoolPerm();
    //@ ensures true;
    
    
{
    return Math.random() < 0.5;
}

}