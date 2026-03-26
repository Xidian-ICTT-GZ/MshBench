class C {
    int x;

    //@ predicate valid() = this.x |-> _;

    C()
    //@ requires true;
    //@ ensures valid();
    {
        //@ close valid();
    }
}

class D extends C {
    int y;

    //@ predicate valid() = super.valid() &*& this.y |-> _;

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

    //@ predicate valid() = super.valid() &*& this.z |-> _;

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
        int r = super.getY();
        //@ close valid();
        return r;
    }
}

class Program {
    static int getY(C c)
    //@ requires c != null &*& c.valid();
    //@ ensures c.valid();
    {
        if (c instanceof D) {
            D d = (D)c;
            //@ open c.valid();
            int r = d.getY();
            //@ close c.valid();
            return r;
        } else {
            //@ open c.valid();
            //@ close c.valid();
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