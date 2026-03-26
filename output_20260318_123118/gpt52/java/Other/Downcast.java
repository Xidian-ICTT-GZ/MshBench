class C {
    int x;

    /*@ predicate c_inv() = this.x |-> ?x; @*/

    //@ requires this != null;
    //@ ensures c_inv();
    C()
    {
    }
}

class D extends C {
    int y;

    /*@ predicate d_inv() = c_inv() &*& this.y |-> ?y; @*/

    //@ requires this != null;
    //@ ensures d_inv();
    D()
    {
    }

    //@ requires this != null &*& d_inv();
    //@ ensures d_inv() &*& result == this.y;
    int getY()
    {
        return this.y;
    }
}

class E extends D {
    int z;

    /*@ predicate e_inv() = d_inv() &*& this.z |-> ?z; @*/

    //@ requires this != null;
    //@ ensures e_inv();
    E()
    {
    }

    //@ requires this != null &*& e_inv();
    //@ ensures e_inv() &*& result == this.y;
    int getY()
    {
        return super.getY();
    }
}

class Program {
    //@ requires c != null &*& c.c_inv();
    //@ ensures c.c_inv();
    static int getY(C c)
    {
        if (c instanceof D) {
            //@ open c_inv();
            //@ close c_inv();
            D d = (D)c;
            //@ assume(d.d_inv());
            int r = d.getY();
            //@ open d.d_inv();
            //@ close d.d_inv();
            return r;
        } else {
            return 0;
        }
    }

    //@ requires true;
    //@ ensures true;
    static void test()
    {
        E e = new E();
        //@ open e.e_inv();
        //@ close e.e_inv();
        getY(e);
        //@ leak e.e_inv();
    }
}