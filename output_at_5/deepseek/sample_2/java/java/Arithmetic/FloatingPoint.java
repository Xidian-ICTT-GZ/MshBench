class Program {

    //@ requires true;
    //@ ensures true;
    public static boolean getRandomBool()
        
        
    {
        //@ assume true;
        return Math.random() < 0.5;
    }

}