class SimpleTermination {

    /*@
    predicate object_inv() = true;
    @*/

    //@ requires true;
    //@ ensures true;
    static void foo()
        
        
    {
        for (int i = 0; i < 10; i++)
            //@ invariant 0 <= i && i <= 10;
        {
        }
    }

    //@ requires true;
    //@ ensures true;
    static void bar()
        
        
    {
        for (int i = 0; i < 10; i++)
            //@ invariant 0 <= i && i <= 10;
        {
            foo();
        }
    }
    
}

class AnotherClass {

    /*@
    predicate this_inv(AnotherClass this) = true;
    @*/

    //@ requires true;
    //@ ensures this_inv(this);
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

    /*@
    predicate this_inv(Foo this) = true;
    @*/

    //@ requires true;
    //@ ensures this_inv(this);
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