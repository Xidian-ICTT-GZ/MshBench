class SimpleTermination {

    //@ requires true;
    //@ ensures true;
    static void foo()
        
        
        
    {
        //@ loop_invariant 0 <= i &*& i <= 10;
        //@ decreases 10 - i;
        for (int i = 0; i < 10; i++)
            
            
        {
        }
    }

    //@ requires true;
    //@ ensures true;
    static void bar()
        
        
        
    {
        //@ loop_invariant 0 <= i &*& i <= 10;
        //@ decreases 10 - i;
        for (int i = 0; i < 10; i++)
            
            
        {
            foo();
        }
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