class C {
    int x;

    /*@
    predicate this_inv(C this) = this->x |-> _;
    @*/

    C()
    //@ requires true;
    //@ ensures this_inv(this);
    {
        //@ close this_inv(this);
    }

}

class D extends C {
    int y;

    /*@
    predicate this_inv(D this) = this->y |-> _ &*& C.this_inv(this);
    @*/

    D()
    //@ requires true;
    //@ ensures this_inv(this);
    {
        //@ close this_inv(this);
    }

    int getY()
    //@ requires this_inv(this);
    //@ ensures this_inv(this) &*& result == this.y;
    {
        //@ open this_inv(this);
        int res = this.y;
        //@ close this_inv(this);
        return res;
    }
}

class E extends D {
    int z;

    /*@
    predicate this_inv(E this) = this->z |-> _ &*& D.this_inv(this);
    @*/

    E()
    //@ requires true;
    //@ ensures this_inv(this);
    {
        //@ close this_inv(this);
    }

    int getY()
    //@ requires this_inv(this);
    //@ ensures this_inv(this) &*& result == super.getY();
    {
        //@ open this_inv(this);
        int res = super.getY();
        //@ close this_inv(this);
        return res;
    }
}

class Program {
    static int getY(C c)
    //@ requires c != null &*& (c instanceof D ? D.this_inv((D)c) : C.this_inv(c));
    //@ ensures (c instanceof D ? D.this_inv((D)c) : C.this_inv(c)) &*& (c instanceof D ? result == ((D)c).getY() : result == 0);
    {
        if (c instanceof D) {
            D d = (D)c;
            //@ open D.this_inv(d);
            int res = d.getY();
            //@ close D.this_inv(d);
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
        //@ open E.this_inv(e);
        getY(e);
        //@ close E.this_inv(e);
    }
}