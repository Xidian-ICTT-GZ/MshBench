class Program {

    //@ ensures true;
    public static boolean getRandomBool()
        
        
    {
        //@ close exists(0.5);
        //@ close exists(Math.random());
        return Math.random() < 0.5;
    }

}