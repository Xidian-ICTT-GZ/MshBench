class C {
    int x;
    
    /*@
    predicate c_inv() = this.x |-> ?x;
    @*/
    
    //@ requires true;
    //@ ensures c_inv();
    C()
        
        
    {
        //@ close c_inv();
    }

    
}

class D extends C {
    int y;

    /*@
    predicate d_inv() = c_inv() &*& this.y |-> ?y;
    @*/
    
    //@ requires true;
    //@ ensures d_inv();
    D()
        
        
    {
        //@ close c_inv();
        //@ close d_inv();
    }
    
    

    
    //@ requires d_inv();
    //@ ensures d_inv() &*& result == this.y;
    int getY()
        
        
    {
        //@ open d_inv();
        int r = this.y;
        //@ close d_inv();
        return r;
        
    }
}

class E extends D {
    int z;
    
    /*@
    predicate e_inv() = d_inv() &*& this.z |-> ?z;
    @*/
    
    //@ requires true;
    //@ ensures e_inv();
    E()
        
        
    {
        //@ close c_inv();
        //@ close d_inv();
        //@ close e_inv();
    }
    
    

    
    //@ requires e_inv();
    //@ ensures e_inv() &*& result == this.y;
    int getY()
        
        
    {
        
        
        //@ open e_inv();
        //@ open d_inv();
        //@ open c_inv();
        //@ close c_inv();
        //@ close d_inv();
        //@ close e_inv();
        return super.getY();
        
        
    }
}

class Program {
    //@ requires true;
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