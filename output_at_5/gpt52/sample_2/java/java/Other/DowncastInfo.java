class C {
    int x;
    
    /*@
    predicate c_inv() = this.x |-> ?x;
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
    predicate d_inv() = this.c_inv() &*& this.y |-> ?y;
    @*/

    D()
        //@ requires true;
        //@ ensures this.d_inv();
    {
        //@ close this.c_inv();
        //@ close this.d_inv();
    }
    
    
    int getY()
        //@ requires this.d_inv();
        //@ ensures this.d_inv();
    {
        //@ open this.d_inv();
        int res = this.y;
        //@ close this.d_inv();
        return res;
        
    }
}

class E extends D {
    int z;
    
    /*@
    predicate e_inv() = this.d_inv() &*& this.z |-> ?z;
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
        //@ requires this.e_inv();
        //@ ensures this.e_inv();
    {
        //@ open this.e_inv();
        //@ open this.d_inv();
        int res = super.getY();
        //@ close this.d_inv();
        //@ close this.e_inv();
        return res;
        
        
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