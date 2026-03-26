class C {
    int x;
    
    //@ predicate valid() = this.x |-> ?v;
    
    C()
    //@ requires true;
    //@ ensures valid();
    {
        //@ close valid();
    }

    
}

class D extends C {
    int y;

    //@ predicate valid() = super.valid() &*& this.y |-> ?v;
    
    D()
    //@ requires true;
    //@ ensures valid();
    {
        //@ close valid();
    }
    
    

    
    int getY()
    //@ requires valid();
    //@ ensures valid() &*& result == this.y;
    {
        //@ open valid();
        return this.y;
        //@ close valid();
    }
}

class E extends D {
    int z;
    
    //@ predicate valid() = super.valid() &*& this.z |-> ?v;
    
    E()
    //@ requires true;
    //@ ensures valid();
    {
        //@ close valid();
    }
    
    

    
    int getY()
    //@ requires valid();
    //@ ensures valid() &*& result == this.y;
    {
        //@ open valid();
        //@ close D.valid();
        return super.getY();
        //@ open D.valid();
        //@ close valid();
    }
}

class Program {
    static int getY(C c)
    //@ requires c.valid();
    //@ ensures c.valid();
    {
        if (c instanceof D) {
            D d = (D)c;
            //@ open C.valid();
            //@ close D.valid();
            int result = d.getY();
            //@ open D.valid();
            //@ close C.valid();
            return result;
        } else {
            return 0;
        }
    }

    static void test()
    //@ requires true;
    //@ ensures true;
    {
        E e = new E();
        //@ open E.valid();
        //@ close C.valid();
        getY(e);
        //@ open C.valid();
        //@ close E.valid();
    }
}