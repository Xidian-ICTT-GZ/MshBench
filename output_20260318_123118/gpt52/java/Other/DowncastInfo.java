class C {
    int x;

    /*@ predicate c_state(C c; int x) = c.x |-> x; @*/

    //@ requires this != null;
    //@ ensures c_state(this, 0);
    C()
    {
    }
}

class D extends C {
    int y;

    /*@ predicate d_state(D d; int x, int y) = c_state(d, x) &*& d.y |-> y; @*/

    //@ requires this != null;
    //@ ensures d_state(this, 0, 0);
    D()
    {
    }

    //@ requires d_state(this, ?x, ?y);
    //@ ensures d_state(this, x, y) &*& result == y;
    int getY()
    {
        return this.y;
    }
}

class E extends D {
    int z;

    /*@ predicate e_state(E e; int x, int y, int z) = d_state(e, x, y) &*& e.z |-> z; @*/

    //@ requires this != null;
    //@ ensures e_state(this, 0, 0, 0);
    E()
    {
    }

    //@ requires e_state(this, ?x, ?y, ?z);
    //@ ensures e_state(this, x, y, z) &*& result == y;
    int getY()
    {
        return super.getY();
    }
}

class Program {
    //@ requires c == null;
    //@ ensures result == 0;
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