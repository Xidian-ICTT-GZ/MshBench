class C {
    int x;
    
    /*@
    predicate CInv() = this.x |-> ?x;
    @*/
    
    //@ requires true;
    //@ ensures CInv();
    C()
        
        
    {
        //@ close CInv();
    }

    
}

class D extends C {
    int y;

    /*@
    predicate DInv() = CInv() &*& this.y |-> ?y;
    @*/
    
    //@ requires true;
    //@ ensures DInv();
    D()
        
        
    {
        //@ close CInv();
        //@ close DInv();
    }
    
    

    
    //@ requires DInv();
    //@ ensures DInv() &*& result == this.y;
    int getY()
        
        
    {
        //@ open DInv();
        int r = this.y;
        //@ close DInv();
        return r;
        
    }
}

class E extends D {
    int z;
    
    /*@
    predicate EInv() = DInv() &*& this.z |-> ?z;
    @*/
    
    //@ requires true;
    //@ ensures EInv();
    E()
        
        
    {
        //@ close CInv();
        //@ close DInv();
        //@ close EInv();
    }
    
    

    
    //@ requires EInv();
    //@ ensures EInv() &*& result == this.y;
    int getY()
        
        
    {
        
        
        //@ open EInv();
        //@ open DInv();
        int r = super.getY();
        //@ close DInv();
        //@ close EInv();
        return r;
        
        
    }
}

class Program {
    //@ requires true;
    //@ ensures true;
    static int getY(C c)
        
        
    {
        if (c instanceof D) {
            D d = (D)c;
            
            //@ assume(d != null);
            //@ assume(d.DInv());
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