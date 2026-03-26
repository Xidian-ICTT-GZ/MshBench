class C {
    int x;
    /*@
    predicate state() = this.x |-> _;
    @*/
    
    C()
        //@ requires true;
        //@ ensures this.state();
        
    {
        //@ close this.state();
    }

    
}

class D extends C {
    int y;
    /*@
    predicate stateD() = this.state() &*& this.y |-> _;
    @*/

    D()
        //@ requires true;
        //@ ensures this.stateD();
        
    {
        //@ close this.state();
        //@ close this.stateD();
    }
    
    

    
    int getY()
        //@ requires this.stateD();
        //@ ensures this.stateD() &*& result == this.y;
        
    {
        //@ open this.stateD();
        
        return this.y;
        
        //@ close this.stateD();
    }
}

class E extends D {
    int z;
    /*@
    predicate stateE() = this.stateD() &*& this.z |-> _;
    @*/
    
    E()
        //@ requires true;
        //@ ensures this.stateE();
        
    {
        //@ close this.state();
        //@ close this.stateD();
        //@ close this.stateE();
    }
    
    

    
    int getY()
        //@ requires this.stateE();
        //@ ensures this.stateE() &*& result == this.y;
        
        
    {
        //@ open this.stateE();
        
        
        return super.getY();
        
        
        //@ close this.stateE();
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