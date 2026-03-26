class SimpleTermination {

    static void foo()
        //@ requires true;
        //@ ensures true;
        
    {
        for (int i = 0; i < 10; i++)
            //@ loop_invariant 0 <= i && i <= 10;
            //@ loop_variant 10 - i;
            
        {
        }
    }

    static void bar()
        //@ requires true;
        //@ ensures true;
        
    {
        for (int i = 0; i < 10; i++)
            //@ loop_invariant 0 <= i && i <= 10;
            //@ loop_variant 10 - i;
            
        {
            foo();
        }
    }
    
}

class AnotherClass {

    AnotherClass()
        //@ requires true;
        //@ ensures this == result;
        
    {}

    static void quux()
        //@ requires true;
        //@ ensures true;
        
    {
        SimpleTermination.bar();
    }

}

class Foo {

    void bar()
        //@ requires true;
        //@ ensures true;
        
    {
        AnotherClass anotherClass = new AnotherClass();
    }

    static void foo()
        //@ requires true;
        //@ ensures true;
        
    {
        Foo foo = new Foo(); 
        
    }

}