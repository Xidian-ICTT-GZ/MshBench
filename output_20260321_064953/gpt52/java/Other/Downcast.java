class C {
    int x;
    //@ predicate inv() = this.x |-> _;
    
    C()
        //@ requires true;
        //@ ensures this.inv();
        
    {
        //@ close this.inv();
    }

    
}

class D extends C {
    int y;
    //@ predicate invD() = this.inv() &*& this.y |-> _;

    D()
        //@ requires true;
        //@ ensures this.invD();
        
    {
        //@ close this.inv();
        //@ close this.invD();
    }
    
    

    
    int getY()
        //@ requires this.invD();
        //@ ensures this.invD() &*& result == this.y;
        
        
    {
        //@ open this.invD();
        int r = this.y;
        //@ close this.invD();
        return r;
        
    }
}

class E extends D {
    int z;
    //@ predicate invE() = this.invD() &*& this.z |-> _;
    
    E()
        //@ requires true;
        //@ ensures this.invE();
        
    {
        //@ close this.inv();
        //@ close this.invD();
        //@ close this.invE();
    }
    
    

    
    int getY()
        //@ requires this.invE();
        //@ ensures this.invE() &*& result == this.y;
        
        
    {
        //@ open this.invE();
        //@ open this.invD();
        //@ close this.invD();
        //@ close this.invE();
        return super.getY();
        
        
    }
}

class Program {
    static int getY(C c)
        //@ requires c != null;
        //@ ensures true;
        
        
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