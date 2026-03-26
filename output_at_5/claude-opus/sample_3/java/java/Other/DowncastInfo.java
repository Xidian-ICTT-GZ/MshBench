class C {
    int x;

    /*@
    predicate C_inv(C c) = c.x |-> _;
    @*/

    C()
    //@ requires true;
    //@ ensures C_inv(this);
    {
        //@ close C_inv(this);
    }

}

class D extends C {
    int y;

    /*@
    predicate D_inv(D d) = d.y |-> _ &*& C_inv(d);
    @*/

    D()
    //@ requires true;
    //@ ensures D_inv(this);
    {
        //@ close D_inv(this);
    }

    int getY()
    //@ requires D_inv(this);
    //@ ensures D_inv(this) &*& result == this.y;
    {
        //@ open D_inv(this);
        int res = this.y;
        //@ close D_inv(this);
        return res;
    }
}

class E extends D {
    int z;

    /*@
    predicate E_inv(E e) = e.z |-> _ &*& D_inv(e);
    @*/

    E()
    //@ requires true;
    //@ ensures E_inv(this);
    {
        //@ close E_inv(this);
    }

    int getY()
    //@ requires E_inv(this);
    //@ ensures E_inv(this) &*& result == super.getY();
    {
        //@ open E_inv(this);
        int res = super.getY();
        //@ close E_inv(this);
        return res;
    }
}

class Program {
    static int getY(C c)
    //@ requires c != null &*& (c instanceof D ? D_inv((D)c) : C_inv(c));
    //@ ensures (c instanceof D ? D_inv((D)c) : C_inv(c)) &*& (c instanceof D ? result == ((D)c).getY() : result == 0);
    {
        if (c instanceof D) {
            D d = (D)c;
            //@ open D_inv(d);
            int res = d.getY();
            //@ close D_inv(d);
            return res;
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