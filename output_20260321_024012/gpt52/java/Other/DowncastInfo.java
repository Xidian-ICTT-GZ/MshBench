class C {
    int x;
    
    //@ predicate c_inv() = this.x |-> ?x;
    
    //@ requires true;
    //@ ensures this.c_inv();
    C()
        
        
    {
        //@ close this.c_inv();
    }

    
}

class D extends C {
    int y;

    //@ predicate d_inv() = this.c_inv() &*& this.y |-> ?y;
    
    //@ requires true;
    //@ ensures this.d_inv();
    D()
        
        
    {
        //@ close this.c_inv();
        //@ close this.d_inv();
    }
    
    

    
    //@ requires this.d_inv();
    //@ ensures this.d_inv() &*& result == this.y;
    int getY()
        
        
    {
        //@ open this.d_inv();
        int result = this.y;
        //@ close this.d_inv();
        return result;
        
    }
}

class E extends D {
    int z;
    
    //@ predicate e_inv() = this.d_inv() &*& this.z |-> ?z;
    
    //@ requires true;
    //@ ensures this.e_inv();
    E()
        
        
    {
        //@ close this.c_inv();
        //@ close this.d_inv();
        //@ close this.e_inv();
    }
    
    

    
    //@ requires this.e_inv();
    //@ ensures this.e_inv() &*& result == this.y;
    int getY()
        
        
    {
        
        //@ open this.e_inv();
        //@ open this.d_inv();
        int result = super.getY();
        //@ close this.d_inv();
        //@ close this.e_inv();
        return result;
        
        
    }
}

class Program {
    //@ requires c instanceof D ? ((D)c).d_inv() : true;
    //@ ensures c instanceof D ? ((D)c).d_inv() : true;
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
        //@ close exists(e);
        E e = new E();
        
        //@ open e.e_inv();
        //@ close e.e_inv();
        getY(e);
    }
}