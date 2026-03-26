package foo;

class Bar {
    public static final short BAR = (byte)0x103;
    public static final short QUUX = (short) (Foo.FOO + BAR);
    public static final short BLA = (short)QUUX;
    
    

    private Bar() 
      
      
    {
      
      this.m(Foo.FOO);
    }
    
    public void m(int s) 
      
      
    {
    }
        
    public static void main(String[] args)
        
        
    {
        short tmp0 = 0;
        tmp0 = BLA;
        assert Foo.FOO == 12345;
        assert BAR == 3;
        assert QUUX == 12348;
        
        
    }
    
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
        
        
    {
        assert Baz.ONE == 1;
    }
}

class BazUser2 implements Baz {
    void instanceMethod()
        
        
    {
        assert TWO == 2;
    }
    
    static void staticMethod()
        
        
    {
        assert TWO == 2;
    }
}