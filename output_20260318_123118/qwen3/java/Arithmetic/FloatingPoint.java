class Program {

    //@ requires true
    //@ ensures true
    public static boolean getRandomBool()
        
        
    {
        return Math.random() < 0.5;
    }

}