class C {
    int x;
    
    //@ predicate inv() = this.x |-> _;
    
    //@ requires true;
    //@ ensures inv();
    C()
        
        
    {
        //@ close inv();
    }

    
}

class D extends C {
    int y;

    //@ predicate inv() = super.inv() &*& this.y |-> _;
    
    //@ requires true;
    //@ ensures inv();
    D()
        
        
    {
        //@ close super.inv();
        //@ close inv();
    }
    
    

    
    //@ requires inv();
    //@ ensures inv();
    int getY()
        
        
    {
        //@ open inv();
        int r = this.y;
        //@ close inv();
        return r;
        
    }
}

class E extends D {
    int z;
    
    //@ predicate inv() = super.inv() &*& this.z |-> _;
    
    //@ requires true;
    //@ ensures inv();
    E()
        
        
    {
        //@ close super.inv();
        //@ close inv();
    }
    
    

    
    //@ requires inv();
    //@ ensures inv();
    int getY()
        
        
    {
        
        
        //@ open inv();
        int r = super.getY();
        //@ close inv();
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