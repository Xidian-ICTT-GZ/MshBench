class C {
    int x;
    
    /*@
    predicate c_state() = this.x |-> _;
    @*/
    
    C()
        //@ requires true;
        //@ ensures this.c_state();
        
        
    {
        //@ close this.c_state();
        
    }

    
}

class D extends C {
    int y;

    /*@
    predicate d_state() = this.c_state() &*& this.y |-> _;
    @*/

    D()
        //@ requires true;
        //@ ensures this.d_state();
        
        
    {
        //@ open this.c_state();
        //@ close this.c_state();
        //@ close this.d_state();
        
    }
    
    

    
    int getY()
        //@ requires this.d_state();
        //@ ensures this.d_state();
        
        
    {
        //@ open this.d_state();
        int r = this.y;
        //@ close this.d_state();
        return r;
        
    }
}

class E extends D {
    int z;
    
    /*@
    predicate e_state() = this.d_state() &*& this.z |-> _;
    @*/
    
    E()
        //@ requires true;
        //@ ensures this.e_state();
        
        
    {
        //@ open this.d_state();
        //@ open this.c_state();
        //@ close this.c_state();
        //@ close this.d_state();
        //@ close this.e_state();
        
    }
    
    

    
    int getY()
        //@ requires this.e_state();
        //@ ensures this.e_state();
        
        
    {
        
        
        //@ open this.e_state();
        int r = super.getY();
        //@ close this.e_state();
        return r;
        
        
    }
}

class Program {
    static int getY(C c)
        //@ requires true;
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