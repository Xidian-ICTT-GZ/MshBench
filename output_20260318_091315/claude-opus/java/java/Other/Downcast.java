class C {
    int x;

    //@ predicate C_inv(C c;) = c.x |-> _;

    C()
        //@ requires true;
        //@ ensures C_inv(this);
    {
        this.x = 0;
    }
}

class D extends C {
    int y;

    //@ predicate D_inv(D d;) = C_inv(d) &*& d.y |-> _;
    //@ requires C_inv(this);
    //@ ensures D_inv(this);
    
    D()
        //@ requires true;
        //@ ensures D_inv(this);
    {
        super();
        this.y = 0;
    }

    //@ requires D_inv(this);
    //@ ensures D_inv(this) &*& result == this.y;
    int getY()
    {
        return this.y;
    }
}

class E extends D {
    int z;

    //@ predicate E_inv(E e;) = D_inv(e) &*& e.z |-> _;
    //@ requires D_inv(this);
    //@ ensures E_inv(this);

    E()
        //@ requires true;
        //@ ensures E_inv(this);
    {
        super();
        this.z = 0;
    }

    //@ requires E_inv(this);
    //@ ensures E_inv(this) &*& result == this.y;
    int getY()
    {
        return super.getY();
    }
}

class Program {
    //@ predicate validC(C c;) = (c instanceof D ? D_inv((D)c) : C_inv(c));

    static int getY(C c)
        //@ requires validC(c);
        //@ ensures validC(c) &*& result == (c instanceof D ? ((D)c).y : 0);
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
        //@ open E_inv(e);
        getY(e);
        //@ close E_inv(e);
    }
}