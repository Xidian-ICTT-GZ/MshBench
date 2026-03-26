class Program {

    //@ requires true;
    //@ ensures true;
    public static boolean getRandomBool()
        
        
    {
        //@ assume false;
        return Math.random() < 0.5;
    }

}