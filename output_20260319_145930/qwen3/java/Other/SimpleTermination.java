/*@ predicate dummy() = true; @*/

class SimpleTermination {

    //@ requires true;
    //@ ensures true;
    static void foo()
        
        
        
    {
        //@ open dummy();
        for (int i = 0; i < 10; i++)
            //@ invariant dummy();
            
            
        {
        }
        //@ close dummy();
    }

    //@ requires true;
    //@ ensures true;
    static void bar()
        
        
        
    {
        //@ open dummy();
        for (int i = 0; i < 10; i++)
            //@ invariant dummy();
            
            
        {
            foo();
        }
        //@ close dummy();
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