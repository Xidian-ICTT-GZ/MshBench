class Program {

    //@ requires true;
    //@ ensures true;
    public static boolean getRandomBool()
        
        
    {
        //@ close Program();
        return Math.random() < 0.5;
    }

    //@ predicate Program() = true;

}