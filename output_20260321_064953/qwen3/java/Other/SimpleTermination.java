class SimpleTermination {

    //@ requires true;
    //@ ensures true;
    static void foo()
        
        
        
    {
        //@ open _();
        for (int i = 0; i < 10; i++)
            
            
        {
        }
        //@ close _();
    }

    //@ requires true;
    //@ ensures true;
    static void bar()
        
        
        
    {
        //@ open _();
        for (int i = 0; i < 10; i++)
            
            
        {
            foo();
        }
        //@ close _();
    }
    
}

class AnotherClass {

    //@ requires true;
    //@ ensures true;
    AnotherClass()
        
        
        
    {}

    //@ requires true;
    //@ ensures true;
    static void quux()
        
        
        
    {
        SimpleTermination.bar();
    }

}

class Foo {

    //@ requires true;
    //@ ensures true;
    void bar()
        
        
        
    {
        AnotherClass anotherClass = new AnotherClass();
    }

    //@ requires true;
    //@ ensures true;
    static void foo()
        
        
        
    {
        Foo foo = new Foo(); 
        
    }

}