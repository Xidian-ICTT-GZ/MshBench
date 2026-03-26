class Program {

//@ predicate randomBoolPerm() = true;

public static boolean getRandomBool()
    //@ requires randomBoolPerm();
    //@ ensures randomBoolPerm() &*& result == true || randomBoolPerm() &*& result == false;
    
{
    return Math.random() < 0.5;
}

}