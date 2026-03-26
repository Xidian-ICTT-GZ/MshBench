class C {
    int x;
    
    /*@
    predicate c_inv() = this.x |-> _;
    @*/
    
    C()
        //@ requires true;
        //@ ensures this.c_inv();
        
        
    {
        //@ close this.c_inv();
        
    }

    
}

class D extends C {
    int y;

    /*@
    predicate d_inv() = this.c_inv() &*& this.y |-> _;
    @*/

    D()
        //@ requires true;
        //@ ensures this.d_inv();
        
        
    {
        //@ close this.c_inv();
        //@ close this.d_inv();
        
    }
    
    

    
    int getY()
        //@ requires this.y |-> ?v;
        //@ ensures this.y |-> v &*& result == v;
        
        
    {
        //@ open this.d_inv();
        
        return this.y;
        
    }
}

class E extends D {
    int z;
    
    /*@
    predicate e_inv() = this.d_inv() &*& this.z |-> _;
    @*/
    
    E()
        //@ requires true;
        //@ ensures this.e_inv();
        
        
    {
        //@ close this.c_inv();
        //@ close this.d_inv();
        //@ close this.e_inv();
        
    }
    
    

    
    int getY()
        //@ requires this.y |-> ?v;
        //@ ensures this.y |-> v &*& result == v;
        
        
    {
        
        
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