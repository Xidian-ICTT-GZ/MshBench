class C {
    int x;
    
    /*@
    predicate c_inv() = this.x |-> ?x;
    @*/
    
    C()
        //@ requires true;
        //@ ensures c_inv();
    {
        //@ close c_inv();
    }

    
}

class D extends C {
    int y;

    /*@
    predicate d_inv() = c_inv() &*& this.y |-> ?y;
    @*/

    D()
        //@ requires true;
        //@ ensures d_inv();
    {
        //@ close c_inv();
        //@ close d_inv();
    }
    
    

    
    int getY()
        //@ requires d_inv();
        //@ ensures d_inv() &*& result == this.y;
    {
        //@ open d_inv();
        int res = this.y;
        //@ close d_inv();
        return res;
        
    }
}

class E extends D {
    int z;
    
    /*@
    predicate e_inv() = d_inv() &*& this.z |-> ?z;
    @*/
    
    E()
        //@ requires true;
        //@ ensures e_inv();
    {
        //@ close c_inv();
        //@ close d_inv();
        //@ close e_inv();
    }
    
    

    
    int getY()
        //@ requires e_inv();
        //@ ensures e_inv() &*& result == this.y;
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