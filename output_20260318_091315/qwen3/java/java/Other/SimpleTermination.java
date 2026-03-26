/*@ predicate world() @*/

class SimpleTermination {

    //@ requires world()
    //@ ensures world()
    static void foo()
        
        
        
    {
        for (int i = 0; i < 10; i++)
            
            
        {
        }
    }

    //@ requires world()
    //@ ensures world()
    static void bar()
        
        
        
    {
        for (int i = 0; i < 10; i++)
            
            
        {
            foo();
        }
    }
    
}

class AnotherClass {

    //@ requires world()
    //@ ensures world()
    AnotherClass()
        
        
        
    {}

    //@ requires world()
    //@ ensures world()
    static void quux()
        
        
        
    {
        SimpleTermination.bar();
    }

}

class Foo {

    //@ requires world()
    //@ ensures world()
    void bar()
        
        
        
    {
        AnotherClass anotherClass = new AnotherClass();
    }

    //@ requires world()
    //@ ensures world()
    static void foo()
        
        
        
    {
        Foo foo = new Foo(); 
        
    }

}