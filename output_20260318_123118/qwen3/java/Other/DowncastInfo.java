//@ predicate C_pred(C c; int x) = c.x |-> x;
//@ predicate D_pred(D d; int x, int y) = C_pred(d, x) &*& d.y |-> y;
//@ predicate E_pred(E e; int x, int y, int z) = D_pred(e, x, y) &*& e.z |-> z;

class C {
    int x;
    
    //@ requires true;
    //@ ensures C_pred(this, 0);
    C()
    {
        this.x = 0;
    }
}

class D extends C {
    int y;

    //@ requires true;
    //@ ensures D_pred(this, 0, 0);
    D()
    {
        super();
        this.y = 0;
    }
    
    //@ requires D_pred(this, ?x, ?y);
    //@ ensures D_pred(this, x, y) &*& result == y;
    int getY()
    {
        return this.y;
    }
}

class E extends D {
    int z;
    
    //@ requires true;
    //@ ensures E_pred(this, 0, 0, 0);
    E()
    {
        super();
        this.z = 0;
    }
    
    //@ requires E_pred(this, ?x, ?y, ?z);
    //@ ensures E_pred(this, x, y, z) &*& result == y;
    int getY()
    {
        return super.getY();
    }
}

class Program {
    //@ requires C_pred(c, ?x) || D_pred(c, ?x, ?y) || E_pred(c, ?x, ?y, ?z);
    //@ ensures result == (c instanceof D ? (c instanceof E ? y : ((D)c).y) : 0);
    //@ ensures (c instanceof D ==> result == ((D)c).y) &*& (!(c instanceof D) ==> result == 0);
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