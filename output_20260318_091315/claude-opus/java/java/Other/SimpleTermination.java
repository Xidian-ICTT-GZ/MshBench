class SimpleTermination {

    //@ requires true;
    //@ ensures true;
    static void foo()
    {
        for (int i = 0; i < 10; i++)
        //@ invariant 0 <= i &*& i <= 10;
        {
        }
    }

    //@ requires true;
    //@ ensures true;
    static void bar()
    {
        for (int i = 0; i < 10; i++)
        //@ invariant 0 <= i &*& i <= 10;
        {
            foo();
        }
    }
    
}

class AnotherClass {

    //@ requires true;
    //@ ensures this!=null;
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
    //@ ensures this!=null;
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