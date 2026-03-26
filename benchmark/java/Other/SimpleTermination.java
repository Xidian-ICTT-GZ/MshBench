class SimpleTermination {

    static void foo()
        
        
        
    {
        for (int i = 0; i < 10; i++)
            
            
        {
        }
    }

    static void bar()
        
        
        
    {
        for (int i = 0; i < 10; i++)
            
            
        {
            foo();
        }
    }
    
}

class AnotherClass {

    AnotherClass()
        
        
        
    {}

    static void quux()
        
        
        
    {
        SimpleTermination.bar();
    }

}

class Foo {

    void bar()
        
        
        
    {
        AnotherClass anotherClass = new AnotherClass();
    }

    static void foo()
        
        
        
    {
        Foo foo = new Foo(); 
        
    }

}