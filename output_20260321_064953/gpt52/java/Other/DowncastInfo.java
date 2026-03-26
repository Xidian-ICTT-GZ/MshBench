class C {
    int x;
    
    /*@
    predicate inv() = this.x |-> ?x;
    @*/
    
    //@ requires true;
    //@ ensures inv();
    C()
        
        
    {
        //@ close inv();
    }

    
}

class D extends C {
    int y;

    /*@
    predicate invD() = this.inv() &*& this.y |-> ?y;
    @*/

    //@ requires true;
    //@ ensures invD();
    D()
        
        
    {
        //@ close inv();
        //@ close invD();
    }
    
    

    
    //@ requires invD();
    //@ ensures invD() &*& result == this.y;
    int getY()
        
        
    {
        //@ open invD();
        int r = this.y;
        //@ close invD();
        return r;
        
    }
}

class E extends D {
    int z;
    
    /*@
    predicate invE() = this.invD() &*& this.z |-> ?z;
    @*/
    
    //@ requires true;
    //@ ensures invE();
    E()
        
        
    {
        //@ close inv();
        //@ close invD();
        //@ close invE();
    }
    
    

    
    //@ requires invE();
    //@ ensures invE() &*& result == this.y;
    int getY()
        
        
    {
        //@ open invE();
        //@ open invD();
        int r = super.getY();
        //@ close invD();
        //@ close invE();
        return r;
        
        
    }
}

class Program {
    //@ requires c != null;
    //@ ensures true;
    static int getY(C c)
        
        
    {
        if (c instanceof D) {
            D d = (D)c;
            
            
            
            //@ assume(d != null);
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