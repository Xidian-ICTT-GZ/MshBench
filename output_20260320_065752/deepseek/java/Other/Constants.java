package foo;

class Bar {
    public static final short BAR = (byte)0x103;
    public static final short QUUX = (short) (Foo.FOO + BAR);
    public static final short BLA = (short)QUUX;
    
    

    private Bar() 
      
      
    {
      //@ close Bar();
      this.m(Foo.FOO);
    }
    
    public void m(int s) 
      //@ requires Bar();
      //@ ensures Bar();
      
    {
    }
        
    public static void main(String[] args)
        //@ requires true;
        //@ ensures true;
        
    {
        short tmp0 = 0;
        tmp0 = BLA;
        assert Foo.FOO == 12345;
        assert BAR == 3;
        assert QUUX == 12348;
        
        
    }
    
    //@ predicate Bar() = true;
}

class Foo {

    private Foo() 
      
      
    {
    }
    public static final int FOO = 12345;
}

interface Baz {
    int ONE = 1;
    int TWO = 2;
}

class BazUser1 {
    static void user()
        //@ requires true;
        //@ ensures true;
        
        
    {
        assert Baz.ONE == 1;
    }
}

class BazUser2 implements Baz {
    void instanceMethod()
        //@ requires true;
        //@ ensures true;
        
        
    {
        assert TWO == 2;
    }
    
    static void staticMethod()
        //@ requires true;
        //@ ensures true;
        
        
    {
        assert TWO == 2;
    }
}