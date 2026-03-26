class C {
    int x;
    
    //@ predicate C() = true;
    
    C()
        //@ requires true;
        //@ ensures C();
    {
        
    }

    
}

class D extends C {
    int y;

    //@ predicate D() = true &*& C();
    
    D()
        //@ requires true;
        //@ ensures D();
    {
        
    }
    
    

    
    int getY()
        //@ requires D();
        //@ ensures result == this.y &*& D();
    {
        
        return this.y;
        
    }
}

class E extends D {
    int z;
    
    //@ predicate E() = true &*& D();
    
    E()
        //@ requires true;
        //@ ensures E();
        
    {
        
    }
    
    

    
    int getY()
        //@ requires E();
        //@ ensures result == super.getY() &*& E();
    {
        
        
        return super.getY();
        
        
    }
}

class Program {
    static int getY(C c)
        //@ requires c != null;
        //@ ensures result >= 0;
    {
        if (c instanceof D) {
            D d = (D)c;
            
            return d.getY();
            
        } else {
            return 0;
        }
    }

    static void test()
        //@ requires true;
        //@ ensures true;
    {
        E e = new E();
        
        getY(e);
    }
}