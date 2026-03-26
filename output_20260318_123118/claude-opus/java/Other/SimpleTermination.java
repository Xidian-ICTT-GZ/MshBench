class SimpleTermination {

    static void foo()
        //@ requires true;
        //@ ensures true;
    {
        for (int i = 0; i < 10; i++)
            //@ invariant 0 <= i &*& i <= 10;
        {
        }
    }

    static void bar()
        //@ requires true;
        //@ ensures true;
    {
        for (int i = 0; i < 10; i++)
            //@ invariant 0 <= i &*& i <= 10;
        {
            foo();
        }
    }
    
}

class AnotherClass {

    AnotherClass()
        //@ requires true;
        //@ ensures true;
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