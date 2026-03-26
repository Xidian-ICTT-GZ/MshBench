class C {
    int x;
    
    /*@
    predicate inv() = this.x |-> _;
    @*/
    
    C()
        
        
    //@ requires true;
    //@ ensures inv();
    {
        //@ close inv();
    }

    
}

class D extends C {
    int y;

    /*@
    predicate inv() = super.inv() &*& this.y |-> _;
    @*/
    
    D()
        
        
    //@ requires true;
    //@ ensures inv();
    {
        //@ close inv();
    }
    
    

    
    int getY()
        
        
    //@ requires inv();
    //@ ensures inv();
    {
        //@ open inv();
        int r = this.y;
        //@ close inv();
        return r;
        
    }
}

class E extends D {
    int z;
    
    /*@
    predicate inv() = super.inv() &*& this.z |-> _;
    @*/
    
    E()
        
        
    //@ requires true;
    //@ ensures inv();
    {
        //@ close inv();
    }
    
    

    
    int getY()
        
        
    //@ requires inv();
    //@ ensures inv();
    {
        
        
        //@ open inv();
        int r = super.getY();
        //@ close inv();
        return r;
        
        
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