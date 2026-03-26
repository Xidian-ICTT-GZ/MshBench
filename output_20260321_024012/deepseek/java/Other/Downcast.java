class C {
    int x;
    
    //@ predicate C() = this.x |-> _;
    
    C()
    //@ requires true;
    //@ ensures C();
    {
        //@ close C();
    }

    
}

class D extends C {
    int y;

    //@ predicate D() = C() &*& this.y |-> _;
    
    D()
    //@ requires true;
    //@ ensures D();
    {
        //@ close D();
    }
    
    

    
    int getY()
    //@ requires D();
    //@ ensures D() &*& result == this.y;
    {
        //@ open D();
        return this.y;
        //@ close D();
    }
}

class E extends D {
    int z;
    
    //@ predicate E() = D() &*& this.z |-> _;
    
    E()
    //@ requires true;
    //@ ensures E();
    {
        //@ close E();
    }
    
    

    
    int getY()
    //@ requires E();
    //@ ensures E() &*& result == this.y;
    {
        //@ open E();
        int r = super.getY();
        //@ close E();
        return r;
    }
}

class Program {
    static int getY(C c)
    //@ requires c.C();
    //@ ensures c.C();
    {
        if (c instanceof D) {
            D d = (D)c;
            //@ open c.C();
            //@ close ((D)c).D();
            int r = d.getY();
            //@ open ((D)c).D();
            //@ close c.C();
            return r;
        } else {
            return 0;
        }
    }

    static void test()
    //@ requires true;
    //@ ensures true;
    {
        E e = new E();
        //@ open e.E();
        //@ close e.D();
        //@ close e.C();
        getY(e);
        //@ open e.C();
        //@ open e.D();
        //@ close e.E();
    }
}