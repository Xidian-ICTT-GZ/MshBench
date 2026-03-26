class C {
    int x;
    
    //@ requires true;
    //@ ensures true;
    C()
        
        
    {
        
    }

    
}

class D extends C {
    int y;

    //@ requires true;
    //@ ensures true;
    D()
        
        
    {
        
    }
    
    

    
    //@ requires true;
    //@ ensures result == this.y;
    int getY()
        
        
    {
        
        return this.y;
        
    }
}

class E extends D {
    int z;
    
    //@ requires true;
    //@ ensures true;
    E()
        
        
    {
        
    }
    
    

    
    //@ requires true;
    //@ ensures result == this.y;
    int getY()
        
        
    {
        
        
        return super.getY();
        
        
    }
}

class Program {
    //@ requires c != null;
    //@ ensures true;
    static int getY(C c)
        
        
    {
        if (c instanceof D) {
            D d = (D)c;
            
            return d.getY();
            
        } else {
            return 0;
        }
    }

    //@ requires true;
    //@ ensures true;
    static void test()
        
        
    {
        E e = new E();
        
        getY(e);
    }
}